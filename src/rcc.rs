use syn::{
    Item,
    ItemFn,
};

use ravenlang::{
    Builder,
    Comp,
    CType,
    CheckedSig,
    Goal,
    HypotheticalCallSyntax,
    HypotheticalCall,
    Op,
    Quantifier,
    RirFn,
    RirFnSig,
    InstRuleSyntax,
    TypeContext,
    VName,
    VType,
    Val,
};

use std::collections::{HashMap, HashSet};

/// The Ravencheck context, which collects definitions, declarations,
/// and verification goals from the user's code.
pub struct Rcc {
    sig: CheckedSig,
    defs: HashMap<String, Comp>,
    goals: Vec<Goal>,
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
        for goal in &self.goals {
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
                self.goals.push(goal);
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

    pub fn reg_multi_annotate<const N: usize>(
        &mut self,
        calls: [&str; N],
        item_fn: &str,
    ) -> Result<(), String> {
        // Parse syn values from strs
        let item_fn: ItemFn = syn::parse_str(item_fn).unwrap();
        let calls: Vec<HypotheticalCallSyntax> = calls
            .into_iter()
            .map(|call| {
                 match syn::parse_str(call) {
                     Ok(call) => Ok(call),
                     Err(e) => Err(format!("Failed to parse #[annotate({})] on item '{}', did you use '->' instead of '=>'? Error: {}", call, item_fn.sig.ident.to_string(), e)),
                 }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Parse the signature into Rir types, and keep the body.
        let i = RirFn::from_syn(item_fn)?;
        let prop_ident = i.sig.ident.clone();
        let calls: Vec<HypotheticalCall> = calls
            .into_iter()
            .map(|call| call.into_rir())
            .collect::<Result<Vec<_>, _>>()?;
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());
        todo!("reg_multi_annotate")
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

    pub fn reg_item_declare(&mut self, item: &str) {
        match syn::parse_str(item).unwrap() {
            Item::Const(i) => self.sig.0.reg_const_declare(i).unwrap(),
            Item::Fn(i) => self.sig.0.reg_fn_declare(i).unwrap(),
            Item::Struct(i) => self.sig.0.reg_struct_declare(i).unwrap(),
            Item::Type(i) => self.sig.0.reg_type_declare(i).unwrap(),
            i => todo!("reg_item_declare for {:?}", i),
        }
    }

    pub fn reg_item_define(&mut self, item: &str, is_rec: bool) {
        match syn::parse_str(item).unwrap() {
            Item::Fn(i) => self.reg_fn_define(i, is_rec).unwrap(),
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
    ) -> Result<(), String>{
        // Parse the signature into Rir types.
        let i = RirFn::from_syn(i)?;
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());
        // Unpack
        let RirFn{sig, body} = i;
        let RirFnSig{ident, tas, inputs, output} = sig.clone();

        // Simplify inputs to VNames (someday I'd like to support
        // patterns...)
        let inputs: Vec<(VName, VType)> = inputs
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
            tc = tc.plus(VName::new(ident.clone()), f_type);
        }

        body.type_check_r(&CType::Return(output.clone()), tc)?;

        let inputs: Vec<(VName, Option<VType>)> = inputs
            .into_iter()
            .map(|(x,t)| (x, Some(t)))
            .collect();
        // Construct function for given typed inputs
        let mut g = body.get_gen();
        let fun: Comp =
            Builder::return_thunk(
                Builder::lift(body).fun(inputs)
            )
            .build(&mut g);

        if is_rec {
            self.sig.0.reg_rir_declare(sig)?;
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
        let i = syn::parse_str(item_fn).unwrap();
        // Parse the ItemFn into Rir types, and keep the body.
        let i = RirFn::from_syn(i).unwrap();
        // Apply type aliases
        let i = i.expand_types(&self.sig.0.type_aliases());
        // Unpack
        let RirFn{sig, body} = i;
        let RirFnSig{ident, tas, inputs, output} = sig;

        // For now, don't allow inputs
        if inputs.len() != 0 {
            panic!(
                "#[verify] items should have zero inputs, but '{}' has {} inputs.",
                ident,
                inputs.len()
            );
        }

        // Declared output must be bool. Consider type aliases and
        // type abstractions when checking.
        if !output.clone().type_match(&VType::prop(), &self.sig.0, &tas) {
            panic!(
                "#[assume] items must have bool output, but '{}' has '{}' output.",
                ident,
                output.render(),
            );
        }

        // Body must also type-check as bool
        let tc = TypeContext::new_types(self.sig.0.clone(), tas.clone());
        match body.type_check_r(&CType::Return(VType::prop()), tc) {
            Ok(()) => {},
            Err(e) => panic!(
                "Type error in '{}': {}", ident, e
            ),
        }

        let goal = Goal {
            title: ident.to_string(),
            tas,
            condition: body,
            should_be_valid,
            
        };

        self.push_goal(goal).unwrap();
    }

    pub fn check_goals(self) {
        let Rcc{sig, goals, ..} = self;
        let mut failures = Vec::new();
        for goal in goals.into_iter() {
            match sig.check_goal(goal) {
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

        let mut igen = def.get_gen();
        f_axiom.advance_gen(&mut igen);

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
        let vc = def.builder().gen_many(
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
                    .seq_gen(|output| {
                        f_axiom.apply_rt(input_vals).apply_rt(vec![output])
                    })
                    .quant(
                        Quantifier::Forall,
                        quant_sig,
                    )
            },
        );
        Ok(vc.build(&mut igen))
    }
}
