use syn::{
    Item,
    ItemFn,
};

use ravenlang::{
    Builder,
    Comp,
    CType,
    CheckedSig,
    Gen,
    Goal,
    HypotheticalCallSyntax,
    Op,
    RirFn,
    RirFnSig,
    InstRuleSyntax,
    TypeContext,
    VName,
    VType,
    block_to_builder,
};

use std::collections::HashMap;

/// The Ravencheck context, which collects definitions, declarations,
/// and verification goals from the user's code.
pub struct Rcc {
    sig: CheckedSig,
    defs: HashMap<String, Comp>,
    goals: Vec<Goal>,
}

impl Rcc {
    pub fn new() -> Self {
        Rcc{
            sig: CheckedSig::empty(),
            defs: HashMap::new(),
            goals: Vec::new(),
        }
    }

    pub fn reg_toplevel_type(&mut self, ident: &str, arity: usize) {
        self.sig.0.sorts.insert(ident.to_string(), arity);
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
    pub fn reg_item_annotate<const N: usize>(
        &mut self,
        call: &str,
        item_fn: &str,
    ) {
        todo!()
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
            Item::Fn(i) => self.sig.0.reg_fn_declare(i).unwrap(),
            Item::Struct(i) => self.sig.0.reg_struct_declare(i).unwrap(),
            Item::Type(i) => self.sig.0.reg_type_declare(i).unwrap(),
            _ => todo!(),
        }
    }

    pub fn reg_item_define(&mut self, item: &str, is_rec: bool) {
        match syn::parse_str(item).unwrap() {
            Item::Fn(i) => self.reg_fn_define(i, is_rec).unwrap(),
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
        let i = i.expand_types(&self.sig.0.type_aliases);
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
        let i = i.expand_types(&self.sig.0.type_aliases);
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

        self.goals.push(goal);
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
}
