use syn::{
    Ident,
    ItemFn,
    ItemStruct,
    ItemType,
    GenericParam,
    Generics,
};

use crate::{
    Axiom,
    BType,
    Builder,
    CType,
    Comp,
    InstRule,
    Gen,
    HypotheticalCall,
    Sig,
    sig::{
        FunOp,
        PredSymbol,
        Op,
        OpCode,
    },
    syn_to_cbpv::{
        InstRuleSyntax,
        HypotheticalCallSyntax,
        RirFnSig,
        block_to_builder,
    },
    type_check::TypeContext,
    VName,
    VType,
};

impl Sig {
    pub fn reg_fn_assume(
        &mut self,
        f: ItemFn,
        inst_rules: Vec<InstRuleSyntax>,
    ) -> Result<(), String> {
        // Parse the signature into Rir types, and keep the body.
        let (RirFnSig{ident, tas, inputs, output}, body) =
            RirFnSig::from_syn(f)?;

        let inst_rules = inst_rules
            .into_iter()
            .map(InstRule::from_syn)
            .collect::<Result<Vec<_>, _>>()?;

        // For now, don't allow inputs
        if inputs.len() != 0 {
            return Err(format!(
                "#[assume] items should have zero inputs, but '{}' has {} inputs.",
                ident,
                inputs.len()
            ));
        }

        // Declared output must be bool. Consider type aliases and
        // type abstractions when checking.
        if !output.clone().type_match(&VType::prop(), self, &tas) {
            return Err(format!(
                "#[assume] items must have bool output, but '{}' has '{}' output.",
                ident,
                output.render(),
            ));
        }

        // Body must also type-check as bool
        let body = match block_to_builder(body) {
            Ok(b) => b.build(&mut Gen::new()),
            Err(e) => return Err(e),
        };
        let tc = TypeContext::new_types(self.clone(), tas.clone());
        match body.type_check_r(&CType::Return(VType::prop()), tc) {
            Ok(()) => {},
            Err(e) => return Err(format!(
                "Type error in '{}': {}", ident, e
            )),
        }
        let axiom = Axiom { tas, inst_rules: inst_rules.clone(), body };
        println!("Pushing axiom with rules {:?}", inst_rules);
        self.axioms.push(axiom);
        Ok(())
    }

    pub fn reg_fn_assume_for(
        &mut self,
        f: ItemFn,
        c: HypotheticalCallSyntax,
    ) -> Result<(), String> {
        // Parse the signature into Rir types, and keep the body.
        let (RirFnSig{ident, mut tas, inputs, output}, body) =
            RirFnSig::from_syn(f)?;
        let HypotheticalCall{code, inputs: c_inputs, output: c_output} =
            c.into_rir()?;

        let applied_op = match self.get_applied_op(&code)? {
            Op::Fun(op) => op,
            op => return Err(format!("#[assume_for(..)] target must be FunOp, got {:?} instead", op)),
        };

        let OpCode{ident: code_ident, types: code_types} = code.clone();

        let code_types: Vec<String> = code_types
            .into_iter()
            .map(|t| match t.unwrap_base() {
                Ok(BType::Prop) => Err(format!("Op can't have bool input")),
                Ok(BType::UI(s, args)) if args.len() == 0 => Ok(s),
                Ok(BType::UI(_, _)) => Err(format!("Type arg in #[assume_for] can't have its own arguments")),
                Err(v) => Err(format!("Type arg {} not allowed in #[assume_for]", v.render())),
            })
            .collect::<Result<Vec<_>,_>>()?;

        if c_inputs.len() != applied_op.inputs.len() {
            return Err(format!("#[assume_for({}(..))] declares {} inputs, while op was declared with {} inputs", code, c_inputs.len(), applied_op.inputs.len()));
        }

        // For now, don't allow inputs
        if inputs.len() != 0 {
            return Err(format!(
                "#[assume_for] items should have zero inputs, but '{}' has {} inputs.",
                ident,
                inputs.len()
            ));
        }

        // For now, don't allow additional tas
        if inputs.len() != 0 {
            return Err(format!(
                "#[assume_for] items should declare zero type arguments , but '{}' declares {} type arguments.",
                ident,
                tas.len()
            ));
        }

        // Add call type args to tas
        tas.append(&mut code_types.clone());

        // Declared output must be bool. Consider type aliases and
        // type abstractions when checking.
        if !output.clone().type_match(&VType::prop(), self, &tas) {
            return Err(format!(
                "#[assume] items must have bool output, but '{}' has '{}' output.",
                ident,
                output.render(),
            ));
        }

        // Body must also type-check as bool, after call inputs and
        // output are added to the context.
        let body = match block_to_builder(body) {
            Ok(b) => b.build(&mut Gen::new()),
            Err(e) => return Err(e),
        };
        let mut tc = TypeContext::new_types(self.clone(), tas.clone());
        // Add call inputs and output to the context.
        tc = tc.append(
            c_inputs
                .iter()
                .zip(applied_op.inputs.iter())
                .map(|(a,b)| (VName::new(a.clone()), b.clone()))
                .collect()
        );
        tc = tc.plus(
            VName::new(c_output.clone()),
            applied_op.output.clone(),
        );
        match body.type_check_r(&CType::Return(VType::prop()), tc) {
            Ok(()) => {},
            Err(e) => return Err(format!(
                "Type error in '{}': {}", ident, e
            )),
        }

        let f_inputs: Vec<(VName, Option<VType>)> = c_inputs
            .iter()
            .zip(applied_op.inputs.iter())
            .map(|(a,b)| (VName::new(a.clone()), Some(b.clone())))
            .collect();
        let f_output = (VName::new(c_output.clone()), Some(applied_op.output.clone()));
        let mut g = body.get_gen();
        let f_axiom: Comp =
            Builder::return_thunk(
                Builder::return_thunk(
                    Builder::lift(body).fun([f_output])
                )
                    .fun(f_inputs)
            ).build(&mut g);

        for (op_name, op_tas, op) in self.ops.iter_mut() {
            let op_tas_types = op_tas
                .clone()
                .into_iter()
                .map(|s| VType::ui(s))
                .collect();
            if op_name == &code_ident {
                match op {
                    Op::Fun(op) => {
                        // todo!("Substitute type arg names");
                        let f_axiom = f_axiom
                            .expand_types_from_call(
                                &op_tas_types,
                                &code_types,
                            )
                            .unwrap();
                        op.axioms.push(f_axiom);
                        return Ok(())
                    }
                    _ => unreachable!(),
                }
            }
        }
        unreachable!()
    }

    pub fn reg_fn_declare(&mut self, f: ItemFn) -> Result<(), String> {
        // Parse the signature into Rir types, and throw away
        // the body.
        let (RirFnSig{ident, tas, inputs, output},_) =
            RirFnSig::from_syn(f)?;
    
        // Throw away the input patterns, keep the types.
        let inputs: Vec<VType> =
            inputs.into_iter().map(|(_,t)| t).collect();
    
        // First, are any inputs thunks, making this a
        // higher-order function?
        let op = if !inputs.iter().any(|i| i.contains_thunk()) {
            // If not, is the output bool?
            if output == VType::prop() {
                // Then this is a simple predicate.
                Op::Symbol(PredSymbol{inputs})
            } else {
                // Else, this is a function. We give it a
                // single axiom, which relates the inputs and
                // outputs using the abstraction relation.
                let code_args = tas
                    .iter()
                    .cloned()
                    .map(VType::ui)
                    .collect();
                let code = OpCode {
                    ident: ident.clone(),
                    types: code_args,
                };
                let axiom = Self::relabs_axiom(
                    code,
                    inputs.clone(),
                    output.clone(),
                );
                Op::Fun(FunOp{
                    inputs,
                    output,
                    axioms: vec![axiom],
                })
            }
        } else {
            // If this is a higher-order function, don't give
            // it the relational abstraction axiom. We will
            // rely on user-supplied axioms.
            if output == VType::prop() {
                todo!("Handle higher-order relations")
            } else {
                Op::Fun(FunOp{
                    inputs,
                    output,
                    axioms: Vec::new(),
                })
            }
        };
        self.ops.push((ident, tas, op));
        Ok(())
    }

    pub fn reg_struct_declare(&mut self, i: ItemStruct) -> Result<(), String> {
        self.declare_type_or_struct(i.ident, i.generics)
    }
    pub fn reg_type_declare(&mut self, i: ItemType) -> Result<(), String> {
        self.declare_type_or_struct(i.ident, i.generics)
    }

    pub fn declare_type_or_struct(
        &mut self,
        ident: Ident,
        generics: Generics,
    ) -> Result<(), String> {
        // Check that only Types are given as GenericParams.
        for p in generics.params.iter() {
            match p {
                GenericParam::Lifetime(..) => {
                    return Err(format!("Lifetime params on declared structs are not supported ({})", ident));
                }
                GenericParam::Type(..) => {}
                GenericParam::Const(..) => {
                    return Err(format!("Const params on declared structs are not supported ({})", ident));
                }
            }
        }

        // We've confirmed that all params are type arguments. The
        // only thing we record is the number of them.
        let arity = generics.params.len();

        self.sorts.insert(ident.to_string(), arity);
        Ok(())
    }
}
