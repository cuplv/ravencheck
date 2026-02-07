use syn::{
    Item,
    ItemFn,
    parse::Parser,
    punctuated::Punctuated,
    PatType,
    Token,
};

use ravenlang::{
    Axiom,
    BType,
    Builder,
    Comp,
    CType,
    CheckedSig,
    IGen,
    Ident as RirIdent,
    InstRule,
    Goal,
    HypotheticalCallSyntax,
    InstMode,
    Op,
    Pattern,
    Quantifier,
    RirFn,
    RirFnSig,
    SolverConfig,
    InstRuleSyntax,
    TypeContext,
    TypeDef,
    VType,
    Val,
};

use std::collections::{HashMap, HashSet};

/// The Ravencheck context, which collects definitions, declarations,
/// and verification goals from the user's code.
pub struct Rcc {
    sig: CheckedSig,
    defs: HashMap<String, Comp>,
    goals: Vec<(Option<CheckedSig>, Goal)>,
    pub seen_hashes: HashSet<u64>,
    solver_config: SolverConfig, 
}

impl Rcc {
    pub fn new() -> Self {
        Rcc{
            sig: CheckedSig::empty(),
            defs: HashMap::new(),
            goals: Vec::new(),
            seen_hashes: HashSet::new(),
            solver_config: SolverConfig::default(),
        }
    }

    pub fn add_solver_arg(&mut self, arg: &str) {
        self.solver_config.add_arg(arg);
    }

    pub fn set_solver(&mut self, name: &str) {
        self.solver_config = SolverConfig::program(name);
    }

    fn get_goal_by_title(&self, title: &str) -> Option<&Goal> {
        for (_, goal) in &self.goals {
            if &goal.title == title {
                return Some(goal);
            }
        }
        None
    }

    fn push_goal(&mut self, goal: Goal) -> Result<(), String> {
        match self.get_goal_by_title(&goal.title) {
            Some(_) =>
                Err(format!("You tried to define '{}' twice", &goal.title)),
            None => {
                self.goals.push((None, goal));
                Ok(())
            }
        }
    }
    fn push_goal_ctx(
        &mut self,
        goal: Goal,
        sig: CheckedSig
    ) -> Result<(), String> {
        match self.get_goal_by_title(&goal.title) {
            Some(_) =>
                Err(format!("You tried to define '{}' twice", &goal.title)),
            None => {
                self.goals.push((Some(sig), goal));
                Ok(())
            }
        }
    }

    pub fn reg_toplevel_type(&mut self, ident: &str, arity: usize) {
        self.sig.0.sorts_insert(ident.to_string(), arity);
    }

    /// Register a function (`fn`) item as a checked annotation.
    ///
    /// # Example
    ///
    /// The following attribute and `fn` item ...
    ///
    /// ```ignore
    /// #[annotate(add::<T>(a, b) => c)]
    /// fn add_is_monotonic() -> bool {
    ///     le::<T>(a, output) && le::<T>(b, output)
    /// }
    /// ```
    ///
    /// ... produces the following `Rcc` method call:
    ///
    /// ```ignore
    /// rcc.reg_item_annotate(
    ///     "add",
    ///     ["a: Nat<T>", "b: Nat<T>"],
    ///     "fn add_is monotonic<T>(output...",
    /// )
    /// ```
    pub fn reg_fn_annotate(
        &mut self,
        call: &str,
        item_fn: &str,
    ) -> Result<(), String> {
        // Parse syn values from str
        let item_fn: ItemFn = syn::parse_str(item_fn).unwrap();
        let call: HypotheticalCallSyntax =
            match syn::parse_str(call) {
                Ok(call) => call,
                Err(e) => panic!("Failed to parse #[annotate({})] on item '{}', did you use '->' instead of '=>'? Error: {}", call, item_fn.sig.ident.to_string(), e),
            };

        // Parse the signature into Rir types, and keep the body.
        let i = RirFn::from_syn(item_fn)?;
        let prop_ident = i.sig.ident.clone();
        let call = call.into_rir()?;
        let call_ident = call.ident.clone();
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());

        // Assume the annotation in the signature.
        let f_axiom = self.sig.0.build_function_axiom(i, call)?;
        self.sig.0.install_function_axiom(&call_ident, f_axiom.clone())?;

        // Build the verification condition to check the annotation.
        let op_tas = self.sig.0.get_tas(&call_ident).unwrap().clone();
        let input_types = self.sig.0
            .get_op_input_types(&call_ident).unwrap().clone();
        let vc = self.build_annotate_vc(&call_ident, input_types, f_axiom)?;

        // Sanity-check that the generated vc is well-formed
        vc.type_check_r(
            &CType::Return(VType::prop()),
            TypeContext::new_types(
                self.sig.0.clone(),
                op_tas.clone()
            )
        ).expect("vc type error");
        self.push_goal(Goal {
            title: prop_ident.clone(),
            tas: op_tas,
            condition: vc,
            should_be_valid: true,
        })?;
        Ok(())
    }

    pub fn reg_fn_inductive<const N1: usize, const N2: usize>(
        &mut self,
        should_fail: bool,
        value_lines: [&str; N1],
        inst_rules: [&str; N2],
        item_fn: &str,
    ) -> Result<(), String> {

        // Parse the inst rules
        let inst_rules = inst_rules.into_iter()
            .map(|s| InstRule::from_syn(syn::parse_str(s).unwrap()))
            .collect::<Result<Vec<_>, _>>()?;

        // Parse syn values from strs
        let item_fn: ItemFn = syn::parse_str(item_fn).unwrap();
        let qsigs: Vec<Punctuated<PatType, Token![,]>> = value_lines
            .into_iter()
            .map(|line| {
                let parser =
                    Punctuated::<PatType, Token![,]>::parse_terminated;
                match parser.parse_str(line) {
                    Ok(line) => Ok(line),
                    Err(e) => Err(format!(
                        "Failed to parse #[for_values({})] on item '{}'. This should look like \"a: Type1, b: Type2, ..\". Error: {}",
                        line,
                        item_fn.sig.ident.to_string(),
                        e,
                    )),
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Parse the signature into Rir types, and keep the body.
        let i = RirFn::from_syn(item_fn)?;
        // Expand type aliases.
        let i = i.expand_types(&self.sig.0.type_aliases());
        let mut igen = IGen::new();
        // Break the parsed fn out into parts.
        let (prop_ident, tas, prop_body) =
            i.into_uni_formula(&mut igen).unwrap();
        let prop_body = prop_body.build_with(&mut igen);

        if tas.len() != 0 && inst_rules.len() == 0 {
            panic!("#[annotate] item '{}' is polymorphic, but has no instantiation rules.  This means that the item, even if verified, will never actually be assumed when verifying other properties.  You need to add a rule to instantiate the item's type parameters when a type of a particular form is relevant.  For example, adding the attribute #[for_type(HashMap<T1,T2> => <T1,T2>)] will plug in T1 and T2 as the item's type parameters when the type HashMap<T1,T2> is used in a query.", prop_ident);
        }

        // let prop_ident = i.sig.ident.clone();
        let mut qsig = Vec::new();
        let mut qbases = Vec::new();
        for punct in qsigs {
            for pair in punct.into_pairs() {
                let pat_type = pair.into_value();
                let (p,t) = Pattern::from_pat_type(pat_type)?;
                let x = p.unwrap_vname()?;
                let t = t.expand_types(&self.sig.0.type_aliases());
                qsig.push((x, t.clone()));
                match t.clone().unwrap_base() {
                    Ok(ref b @ BType::UI(ref t_ident, _)) => {
                        match self.sig.0.type_defs.get(t_ident) {
                            Some((_, TypeDef::Enum(..))) => {},
                            _ => return Err(format!("{}: only enum types should be used in #[inductive(..)], but you used {} for property {}", prop_ident, t.render(), &prop_ident)),
                        }
                        qbases.push(b.clone());
                    }
                    Ok(BType::Prop) => return Err(format!("{}: only enum types should be used in #[inductive(..)], but you used {} for property {}", prop_ident, t.render(), &prop_ident)),
                    Err(t) => return Err(format!("{}: only enum types should be used in #[inductive(..)], but you used {} for property {}", prop_ident, t.render(), &prop_ident)),
                }
            }
        }

        // Create a snapshot of the sig which does not assume the
        // property under verification.  This sig marks the quantified
        // base types as inductive, so that their substruct relations
        // are defined and axiomatized.
        let mut qbases_set = HashSet::new();
        for b in &qbases {
            qbases_set.insert(b.clone());
        }
        let mut vc_sig = self.sig.clone();
        vc_sig.0.inductive_bases = Some(qbases_set);

        let axiom_body = prop_body.clone()
            .erase_wildcard_lets();
        let axiom_body_clone = axiom_body.clone();
        let axiom = axiom_body.builder()
            .into_quantifier(Quantifier::Forall, qsig.clone())
            .build_with(&mut igen);

        // Sanity-check that the generated axiom is well-formed
        axiom.type_check_r(
            &CType::Return(VType::prop()),
            TypeContext::new_types(
                self.sig.0.clone(),
                tas.clone(),
            )
        ).expect(&format!(
            "type error in generated vc for '{}'",
            &prop_ident,
        ));

        let top_xs: Vec<RirIdent> =
            qsig.iter().map(|(x,_)| x.clone()).collect();
        let inhyp = Builder::with_x_many(qbases.len(), |hyp_xs| {
            let rs: Vec<((BType, RirIdent), RirIdent)> = qbases.into_iter()
                .zip(hyp_xs)
                .zip(top_xs)
                .collect();

            let hyp_le_top: Vec<Builder> = rs.iter()
                .cloned()
                .map(|((bt,hx),tx)| {
                    Builder::is_substruct_v(
                        bt,
                        hx.val(),
                        tx.val()
                    )
                }).collect();

            let hyp_smaller_top: Vec<Builder> = rs.iter()
                .cloned()
                .map(|((_bt,hx),tx)| {
                     Builder::is_ne_v(hx.val(), tx.val())
                })
                .collect();

            // Create the inductive hypothesis body by subbing the
            // hypothetical substructure variables into the axiom
            // body.
            let inhyp_body = axiom_body_clone.substitute_many(
                &rs.iter()
                    .map(|((_,hx),tx)| (tx.clone(), hx.clone().val()))
                    .collect()
            );

            // Create the quantifier signature for the hypothetical
            // substructure variables.
            let inhyp_sig: Vec<(RirIdent, VType)> = rs.into_iter()
                .map(|((bt,hx),_tx)| (hx, VType::Base(bt)))
                .collect();

            // Every hyp_x must be substructure of its corresponding
            // top_x (that is, equal to it or a smaller part of it).
            Builder::and_many(hyp_le_top)
            // At least one hyp_x must be a proper substructure of its
            // corresponding top_x (not equal to it).
                .and(Builder::or_many(hyp_smaller_top))
            // Under those conditions, assume that the property holds
            // for the hypothetical substructure variables.
            //
            // Use undef_or so that calls in the assumption do not
            // create sort edges.
                .implies(
                    inhyp_body.builder().into_undef_or()
                )
            // Wrap it all in a quantifier for the hypothetical
            // substructure variables.
                .into_quantifier(Quantifier::Forall, inhyp_sig)
        });


        // IF this annotation is not intended to fail, assume the
        // property in the main sig.
        if !should_fail {
            self.sig.0.axioms.push(Axiom {
                tas: Vec::new(),
                inst_mode: InstMode::Rules(inst_rules),
                body: axiom,
            });
        }

        // Then build the verification condition.

        // Again, forall-quantify the input values.

        // Sequence the body that each call refers to, to the given
        // output variable.

        let vc = inhyp.implies(prop_body.unroll_rec(&self.defs, &mut igen).builder())
            .into_quantifier(Quantifier::Forall, qsig)
            .build_with(&mut igen);

        // Sanity-check that the generated vc is well-formed
        vc.type_check_r(
            &CType::Return(VType::prop()),
            TypeContext::new_types(
                vc_sig.0.clone(),
                tas.clone(),
            )
        ).expect("vc type error");

        // Push the property as a goal, using the vc_sig (which does
        // not assume the property) to eventually perform the
        // verification.
        self.push_goal_ctx(
            Goal {
                title: prop_ident.clone(),
                tas,
                condition: vc,
                should_be_valid: !should_fail,
            },
            vc_sig,
        )?;
        Ok(())
    }

    pub fn reg_fn_assume<const N: usize>(
        &mut self,
        inst_rules: [&str; N],
        item_fn: &str,
    ) {
        
        let mut inst_rules_parsed: Vec<InstRuleSyntax> = Vec::new();
        for s in inst_rules {
            inst_rules_parsed.push(syn::parse_str(s).unwrap());
        }

        let item_fn = syn::parse_str(item_fn).unwrap();
        self.sig.0.reg_fn_assume(item_fn, inst_rules_parsed).unwrap();
    }

    pub fn reg_fn_assume_for(
        &mut self,
        call: &str,
        item_fn: &str,
    ) {
        let item_fn: ItemFn = syn::parse_str(item_fn).unwrap();
        let call: HypotheticalCallSyntax =
            match syn::parse_str(call) {
                Ok(call) => call,
                Err(e) => panic!("Failed to parse #[assume({})] on item '{}', did you use '->' instead of '=>'? Error: {}", call, item_fn.sig.ident.to_string(), e),
            };
        self.sig.0.reg_fn_assume_for(item_fn, call).unwrap();
    }

    pub fn reg_item_declare(&mut self, item: &str, is_total: bool) {
        match syn::parse_str(item).unwrap() {
            Item::Const(i) => self.sig.0.reg_const_declare(i).unwrap(),
            Item::Fn(i) => self.sig.0.reg_fn_declare(i, is_total).unwrap(),
            Item::Struct(i) => self.sig.0.reg_struct_declare(i).unwrap(),
            Item::Type(i) => self.sig.0.reg_type_declare(i).unwrap(),
            i => todo!("reg_item_declare for {:?}", i),
        }
    }

    pub fn reg_item_define(&mut self, item: &str, is_rec: bool, is_total: bool) {
        match syn::parse_str(item).unwrap() {
            Item::Fn(i) => self.reg_fn_define(i, is_rec, is_total).unwrap(),
            Item::Enum(i) => self.sig.0.reg_enum_define(i, is_rec).unwrap(),
            Item::Type(i) if !is_rec =>
                self.sig.0.reg_type_define(i).unwrap(),
            i if is_rec => panic!("Cannot recursive-define {:?}", i),
            i => panic!("Cannot define {:?}", i),
        }
    }

    fn reg_fn_define(
        &mut self,
        i: ItemFn,
        is_rec: bool,
        is_bool: bool,
    ) -> Result<(), String>{
        // Parse the signature into Rir types.
        let i = RirFn::from_syn(i)?;
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());
        // Unpack
        let RirFn{sig, body} = i;
        let RirFnSig{ident, tas, inputs, output} = sig.clone();

        // Simplify inputs to RirIdents (someday I'd like to support
        // patterns...)
        let inputs: Vec<(RirIdent, VType)> = inputs
            .into_iter()
            .map(|(p,t)| Ok((p.unwrap_vname()?, t)))
            .collect::<Result<Vec<_>, String>>()?;

        // Typecheck body, given typed inputs
        let mut tc = TypeContext::new_types(self.sig.0.clone(), tas.clone());
        for (x,t) in inputs.clone().into_iter() {
            tc = tc.plus(x, t);
        }

        if is_rec {
            let f_type = VType::fun_v(
                inputs
                    .clone()
                    .into_iter()
                    .map(|(_,t)| t)
                    .collect::<Vec<_>>(),
                output.clone(),
            );
            tc = tc.plus(RirIdent::new(ident.clone()), f_type);
        }

        body.type_check_r(&CType::Return(output.clone()), tc)?;

        // Construct function for given typed inputs
        let mut g = body.get_igen();
        let fun: Comp =
            Builder::return_thunk(
                Builder::lift(body).into_fun(inputs)
            )
            .build_with(&mut g);

        if is_rec {
            self.sig.0.reg_rir_declare(sig, is_bool)?;
            self.defs.insert(ident.clone(), fun);
            Ok(())
        } else {
            self.sig.0.ops.push((ident, tas, Op::Direct(fun)));
            Ok(())
        }
    }

    pub fn reg_item_import(&mut self, _item: &str) {
        todo!()
    }

    pub fn reg_fn_goal(&mut self, should_be_valid: bool, item_fn: &str) {
        let attr_str = if should_be_valid {
            "#[verify]"
        } else {
            "#[falsify]"
        };

        let i = syn::parse_str(item_fn).unwrap();
        // Parse the ItemFn into Rir types, and keep the body.
        let i = RirFn::from_syn(i).unwrap();
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());
        // Typecheck as bool
        i.type_check(&self.sig.0, false).unwrap();
        assert!(
            i.sig.output == VType::prop(),
            "{attr_str} items should have output type 'bool', but {} had {}",
            i.sig.ident,
            i.sig.output.render(),
        );

        // Create a forall-quantified formula, which quantifies the fn
        // item's arguments.
        let mut igen = IGen::new();
        let (ident, tas, formula) = i.into_uni_formula(&mut igen).unwrap();

        let goal = Goal {
            title: ident,
            tas,
            condition: formula.build_with(&mut igen),
            should_be_valid,
            
        };

        self.push_goal(goal).unwrap();
    }

    pub fn check_goals(self) {
        let Rcc{sig, goals, solver_config, ..} = self;
        let mut failures = Vec::new();
        for (ctx,goal) in goals.into_iter() {
            let specific_sig = match ctx {
                Some(goal_sig) => goal_sig,
                None => sig.clone(),
            };
            match specific_sig.check_goal(goal, &solver_config) {
                Ok(()) => {},
                Err(e) => failures.push(e),
            }
        }
        if failures.len() > 0 {
            let mut s = String::new();
            s.push_str("\n");
            s.push_str("#########[ verification failed ]#########\n");
            s.push_str("##\n");
            for e in failures {
                s.push_str(&format!("## > {}\n", e));
                s.push_str("##\n");
            }
            s.push_str("#########################################\n");

            panic!("{}", s);
        }
    }

    fn build_annotate_vc(
        &self,
        ident: &str,
        input_types: Vec<VType>,
        f_axiom: Comp,
    ) -> Result<Comp, String> {
        let def = match self.defs.get(ident) {
            Some(def) => Ok(def.clone()),
            None => Err(format!("Cannot check annotation on '{}', because no definition found for '{}'. Did you forget to use #[recursive]?", ident, ident)),
        }?;

        let mut igen = def.get_igen();
        f_axiom.advance_igen(&mut igen);
        let f_axiom = f_axiom.rename(&mut igen);

        // Define a condition that...
        //
        // 1. Forall-quantifies the operation inputs.
        //
        // 2. Produces the output by applying the inputs to the
        // operation's definition function.
        //
        // 3. Applies the inputs and the output to the function axiom.
        //
        // What about type abstractions? Use the operation's tas. The
        // function axiom has already subbed those in.
        let f_axiom = f_axiom.builder();
        let input_count = input_types.len();
        let vc = def.builder().igen_many(
            input_count,
            |def| |xs| {
                let input_vals: Vec<Val> = xs
                    .clone()
                    .into_iter()
                    .map(|x| x.val())
                    .collect();
                let quant_sig = xs
                    .into_iter()
                    .zip(input_types)
                    .collect::<Vec<_>>();
                def
                    .apply_rt(input_vals.clone())
                    .seq_igen(|output| {
                        f_axiom.apply_rt(input_vals).apply_rt(vec![output])
                    })
                    .into_quantifier(
                        Quantifier::Forall,
                        quant_sig,
                    )
            },
        );
        Ok(vc.build_with(&mut igen))
    }
}
