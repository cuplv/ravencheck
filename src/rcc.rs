use syn::{
    Expr,
    Item,
    ItemFn,
    parse::Parser,
    punctuated::Punctuated,
    PatType,
    Token,
};

use ravenlang::{
    Axiom,
    Builder,
    Comp,
    CType,
    CheckedSig,
    IGen,
    Goal,
    HypotheticalCallSyntax,
    HypotheticalCall,
    InstMode,
    Op,
    OpCode,
    Pattern,
    Quantifier,
    RirFn,
    RirFnSig,
    InstRuleSyntax,
    TypeContext,
    Ident as RirIdent,
    VType,
    Val,
    syn_to_builder,
};

use std::collections::{HashMap, HashSet};

/// The Ravencheck context, which collects definitions, declarations,
/// and verification goals from the user's code.
pub struct Rcc {
    sig: CheckedSig,
    defs: HashMap<String, Comp>,
    goals: Vec<(Option<CheckedSig>, Goal)>,
    touched_paths: HashSet<String>,
}

impl Rcc {
    pub fn new() -> Self {
        Rcc{
            sig: CheckedSig::empty(),
            defs: HashMap::new(),
            goals: Vec::new(),
            touched_paths: HashSet::new(),
        }
    }

    pub fn touch_new_path(&mut self, path: &str) -> bool {
        if self.touched_paths.contains(path) {
            false
        } else {
            self.touched_paths.insert(path.to_string());
            true
        }
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

    pub fn reg_fn_annotate_multi<const N1: usize, const N2: usize, const N3: usize>(
        &mut self,
        should_fail: bool,
        value_lines: [&str; N1],
        call_lines: [&str; N2],
        inst_lines: [&str; N3],
        item_fn: &str,
    ) -> Result<(), String> {
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
        let calls: Vec<HypotheticalCallSyntax> = call_lines
            .into_iter()
            .map(|call| {
                 match syn::parse_str(call) {
                     Ok(call) => Ok(call),
                     Err(e) => Err(format!(
                         "Failed to parse #[for_call({})] on item '{}', did you use '->' instead of '=>'? Error: {}",
                         call,
                         item_fn.sig.ident.to_string(),
                         e,
                     )),
                 }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let insts: Vec<Expr> = inst_lines
            .into_iter()
            .map(|inst| {
                match syn::parse_str(inst) {
                    Ok(inst) => Ok(inst),
                    Err(e) => Err(format!(
                        "Failed to parse #[for_inst({})] on item '{}'. This should be a Rust expression. Error: {}",
                        inst,
                        item_fn.sig.ident.to_string(),
                        e,
                    )),
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Parse the signature into Rir types, and keep the body.
        let i = RirFn::from_syn(item_fn)?;
        let prop_ident = i.sig.ident.clone();
        let mut qsig = Vec::new();
        for punct in qsigs {
            for pair in punct.into_pairs() {
                let pat_type = pair.into_value();
                let (p,t) = Pattern::from_pat_type(pat_type)?;
                let x = p.unwrap_vname()?;
                let t = t.expand_types(&self.sig.0.type_aliases());
                qsig.push((x,t));
            }
        }
        let calls: Vec<HypotheticalCall> = calls
            .into_iter()
            .map(|call| {
                let call = call.into_rir();
                call
            })
            .collect::<Result<Vec<_>, _>>()?;

        let insts: Vec<Builder> = insts
            .into_iter()
            .map(|inst| {
                let b = syn_to_builder(inst)?;
                Ok::<Builder, String>(b)
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());

        // Build the axiom.

        // Forall-quantify all input values.

        // Sequence each call to the given output variable.

        // The fn item body goes on bottom.
        let code_calls: Vec<(Builder, RirIdent)> = calls
            .iter()
            .map(|call| {
                let vs = call.inputs
                    .iter()
                    .map(|s| RirIdent::new(s).val())
                    .collect::<Vec<_>>();
                let b = call.code().as_fun().builder().apply_rt(vs);
                (b, RirIdent::new(&call.output))
            })
            .collect();

        let mut igen = i.body.get_igen();
        let axiom_body = i.body.clone().builder();
        let axiom =
            Builder::seq_many(code_calls, |_| axiom_body)
            .quant(Quantifier::Forall, qsig.clone())
            .build_with(&mut igen);

        // Sanity-check that the generated axiom is well-formed
        axiom.type_check_r(
            &CType::Return(VType::prop()),
            TypeContext::new_types(
                self.sig.0.clone(),
                Vec::new(),
            )
        ).expect(&format!(
            "type error in generated vc for '{}'",
            &prop_ident,
        ));

        let guarded_axiom = axiom
            .clone()
            .builder()
            .guard_recursive()
            .build_with(&mut igen);

        // Create a temporary sig which assumes the recursion-guarded
        // version of the axiom, and is prepared to add recursion
        // guards to the expanded definitions.
        let mut vc_sig = self.sig.clone();
        let recs: HashSet<OpCode> =
            calls.iter().map(|c| OpCode::fun_types(c.ident.clone(), Vec::new())).collect();
        vc_sig.0.recs = Some(recs);
        vc_sig.0.axioms.push(Axiom {
            tas: Vec::new(),
            inst_mode: InstMode::Rules(Vec::new()),
            body: guarded_axiom,            
        });

        // IF this annotation is not intended to fail, assume the
        // non-guarded axiom in the main sig.
        if !should_fail {
            self.sig.0.axioms.push(Axiom {
                tas: Vec::new(),
                inst_mode: InstMode::Rules(Vec::new()),
                body: axiom,
            });
        }


        // Then build the verification condition.

        // Again, forall-quantify the input values.

        // Sequence the body that each call refers to, to the given
        // output variable.

        // The fn item body goes on bottom, again.
        let def_calls: Vec<(Builder, RirIdent)> = calls
            .iter()
            .map(|call| {
                let vs = call.inputs
                    .iter()
                    .map(|s| RirIdent::new(s).val())
                    .collect();
                let def = match self.defs.get(&call.ident) {
                    Some(def) => Ok(def.clone()),
                    None => Err(format!("Cannot check annotation '{}', because no definition found for '{}'. Did you forget to use #[recursive]?", prop_ident, &call.ident)),
                }?;
                let def = def.rename(&mut igen);
                def.advance_igen(&mut igen);
                let b = def.builder().apply_rt(vs);
                Ok::<(Builder,RirIdent), String>((b, RirIdent::new(&call.output)))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // In the verification condition, we bind the
        // quantifier-instantiation expressions to fresh variables
        // that are then never referenced in the body.
        //
        // These come after the inductive-expansion calls, so that
        // they can reference the outputs of those.
        let vc =
            Builder::seq_many(def_calls, |_| {
                Builder::seq_many_igen(insts, |_| {
                    i.body.builder()
                })
            })
            .quant(Quantifier::Forall, qsig)
            .build_with(&mut igen);
        // Sanity-check that the generated vc is well-formed
        vc.type_check_r(
            &CType::Return(VType::prop()),
            TypeContext::new_types(
                self.sig.0.clone(),
                Vec::new(),
            )
        ).expect("vc type error");
        println!("Just type-checked this vc: {:?}", vc);

        // Push the goal, using the special vc_sig to eventually
        // perform the verification.
        self.push_goal_ctx(
            Goal {
                title: prop_ident.clone(),
                tas: Vec::new(),
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
        let (ident, tas, formula) = i.into_uni_formula().unwrap();

        let goal = Goal {
            title: ident,
            tas,
            condition: formula.build_with(&mut IGen::new()),
            should_be_valid,
            
        };

        self.push_goal(goal).unwrap();
    }

    pub fn check_goals(self) {
        let Rcc{sig, goals, ..} = self;
        let mut failures = Vec::new();
        for (ctx,goal) in goals.into_iter() {
            let specific_sig = match ctx {
                Some(goal_sig) => goal_sig,
                None => sig.clone(),
            };
            match specific_sig.check_goal(goal) {
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
                    .quant(
                        Quantifier::Forall,
                        quant_sig,
                    )
            },
        );
        Ok(vc.build_with(&mut igen))
    }
}
