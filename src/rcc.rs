use syn::{
    Item,
};

use ravenlang::{
    CType,
    Comp,
    CheckedSig,
    Gen,
    Goal,
    RirFnSig,
    InstRuleSyntax,
    TypeContext,
    VType,
    block_to_builder,
};

/// The Ravencheck context, which collects definitions, declarations,
/// and verification goals from the user's code.
pub struct Rcc {
    sig: CheckedSig,
    goals: Vec<Goal>,
}

impl Rcc {
    pub fn new() -> Self {
        Rcc{
            sig: CheckedSig::empty(),
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
    /// #[annotate(add::<T>(a, b) ~> c)]
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
        target_name: &str,
        inputs: [&str; N],
        item: &str,
    ) {
        todo!()
    }

    pub fn reg_item_assume_for<const N: usize>(
        &mut self,
        target_name: &str,
        inputs: [&str; N],
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

    pub fn reg_item_declare(&mut self, item: &str) {
        match syn::parse_str(item).unwrap() {
            Item::Fn(i) => self.sig.0.reg_fn_declare(i).unwrap(),
            Item::Struct(i) => self.sig.0.reg_struct_declare(i).unwrap(),
            Item::Type(i) => self.sig.0.reg_type_declare(i).unwrap(),
            _ => todo!(),
        }
    }

    pub fn reg_item_define(&mut self, item: &str) {
        todo!()
    }

    pub fn reg_item_define_rec(&mut self, item: &str) {
        todo!()
    }

    pub fn reg_item_import(&mut self, item: &str) {
        todo!()
    }

    pub fn reg_fn_goal(&mut self, should_be_valid: bool, item_fn: &str) {
        let i = syn::parse_str(item_fn).unwrap();
        // Parse the signature into Rir types, and keep the body.
        let (RirFnSig{ident, tas, inputs, output}, body) =
            RirFnSig::from_syn(i).unwrap();

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
        let body = match block_to_builder(body) {
            Ok(b) => b.build(&mut Gen::new()),
            Err(e) => panic!("{}", e),
        };
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
