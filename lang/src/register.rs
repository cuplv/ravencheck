use syn::{
    Fields,
    Ident as SynIdent,
    ItemConst,
    ItemEnum,
    ItemFn,
    ItemStruct,
    ItemType,
    GenericParam,
    Generics,
};

use crate::{
    Axiom,
    Builder,
    CType,
    Comp,
    constructions,
    Gen,
    InstMode,
    InstRule,
    HypotheticalCall,
    Sig,
    sig::{
        ConstOp,
        FunOp,
        PredSymbol,
        Op,
        OpCode,
    },
    syn_to_cbpv::{
        InstRuleSyntax,
        HypotheticalCallSyntax,
        RirFn,
        RirFnSig,
    },
    type_check::TypeContext,
    Ident as RirIdent,
    VType,
};

use std::collections::HashMap;

impl Sig {
    pub fn reg_const_declare(
        &mut self,
        i: ItemConst,
    ) -> Result<(), String> {
        let ItemConst{ident, ty, ..} = i;
        let op = Op::Const(ConstOp{
            vtype: VType::from_syn(*ty)?,
        });
        self.ops.push((
            ident.to_string(),
            Vec::new(),
            op,
        ));
        Ok(())
    }

    pub fn reg_enum_declare(&mut self, i: ItemEnum) -> Result<(), String> {
        self.declare_type_or_struct(i.ident, i.generics)
    }

    pub fn reg_enum_define(
        &mut self,
        i: ItemEnum,
        // todo: validate variants types, depending on whether recursive was used
        _is_rec: bool,
    ) -> Result<(), String> {
        let mut tas = Vec::new();
        // Check that only Types are given as GenericParams.
        for p in i.generics.params.iter() {
            match p {
                GenericParam::Lifetime(..) => {
                    return Err(format!("Lifetime params on declared structs are not supported ({})", i.ident));
                }
                GenericParam::Type(tp) => {
                    tas.push(tp.ident.to_string());
                }
                GenericParam::Const(..) => {
                    return Err(format!("Const params on declared structs are not supported ({})", i.ident));
                }
            }
        }
        let mut variants = HashMap::new();
        for variant in i.variants.iter() {
            match &variant.fields {
                Fields::Named(_) => return Err(format!("Defining named enum fields is not supported ({})", i.ident)),
                Fields::Unnamed(fields) => {
                    let mut ts = Vec::new();
                    for f in fields.unnamed.iter() {
                        ts.push(VType::from_syn(f.ty.clone())?);
                    }
                    variants.insert(variant.ident.to_string(), ts);
                }
                Fields::Unit => {
                    variants.insert(variant.ident.to_string(), Vec::new());
                }
            }
        }
        self.type_sums_insert(i.ident.to_string(), tas, variants);
        Ok(())
    }

    pub fn reg_fn_assume(
        &mut self,
        i: ItemFn,
        inst_rules: Vec<InstRuleSyntax>,
    ) -> Result<(), String> {
        // Parse the ItemFn into Rir types, and keep the body.
        let i = RirFn::from_syn(i)?;
        // Apply type aliases
        let i = i.expand_types(&self.type_aliases());
        // Unpack
        let RirFn{sig, body} = i;
        let RirFnSig{ident, tas, inputs, output} = sig;

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
        let tc = TypeContext::new_types(self.clone(), tas.clone());
        match body.type_check_r(&CType::Return(VType::prop()), tc) {
            Ok(()) => {},
            Err(e) => return Err(format!(
                "Type error in '{}': {}", ident, e
            )),
        }
        let axiom = Axiom {
            tas,
            inst_mode: InstMode::Rules(inst_rules.clone()),
            body,
        };
        // println!("Pushing axiom with rules {:?}", inst_rules);
        self.axioms.push(axiom);
        Ok(())
    }

    pub fn build_function_axiom(
        &mut self,
        i: RirFn,
        c: HypotheticalCall,
    ) -> Result<Comp, String> {
        // Assume that type aliases have already been applied.
        // Unpack
        let RirFn{sig, body} = i;
        let RirFnSig{ident, mut tas, inputs, output} = sig;
        let c_code = c.code();
        let HypotheticalCall{
            ident: c_ident,
            tas: c_tas,
            inputs: c_inputs,
            output: c_output
        } = c;

        let applied_op = match self.get_applied_op(&c_code)? {
            Op::Fun(op) => op,
            op => return Err(format!("#[assume_for(..)] target must be FunOp, got {:?} instead", op)),
        };

        if c_inputs.len() != applied_op.inputs.len() {
            return Err(format!("#[assume_for({}(..))] declares {} inputs, while op was declared with {} inputs", c_code, c_inputs.len(), applied_op.inputs.len()));
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
        tas.append(&mut c_tas.clone());

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
        let mut tc = TypeContext::new_types(self.clone(), tas.clone());
        // Add call inputs and output to the context.
        tc = tc.append(
            c_inputs
                .iter()
                .zip(applied_op.inputs.iter())
                .map(|(a,b)| (RirIdent::new(a.clone()), b.clone()))
                .collect()
        );
        tc = tc.plus(
            RirIdent::new(c_output.clone()),
            applied_op.output.clone(),
        );
        match body.type_check_r(&CType::Return(VType::prop()), tc) {
            Ok(()) => {},
            Err(e) => return Err(format!(
                "Type error in '{}': {}", ident, e
            )),
        }

        let f_inputs: Vec<(RirIdent, Option<VType>)> = c_inputs
            .iter()
            .zip(applied_op.inputs.iter())
            .map(|(a,b)| (RirIdent::new(a.clone()), Some(b.clone())))
            .collect();
        let f_output = (RirIdent::new(c_output.clone()), Some(applied_op.output.clone()));
        let mut g = body.get_gen();
        let f_axiom: Comp =
            Builder::return_thunk(
                Builder::return_thunk(
                    Builder::lift(body).fun([f_output])
                )
                    .fun(f_inputs)
            ).build(&mut g);

        // Replace hypothetical call type argument names with the
        // declared operation's type argument names.
        let op_tas_types = self
            .get_tas(&c_ident)
            .unwrap()
            .iter()
            .cloned()
            .map(VType::ui)
            .collect();
        let f_axiom = f_axiom
            .expand_types_from_call(&op_tas_types, &c_tas)
            .unwrap();

        Ok(f_axiom)
    }

    pub fn reg_fn_assume_for(
        &mut self,
        i: ItemFn,
        c: HypotheticalCallSyntax,
    ) -> Result<(), String> {
        // Parse the signature into Rir types, and keep the body.
        let i = RirFn::from_syn(i)?;
        // Apply type aliases
        let i = i.expand_types(&self.type_aliases());
        // Parse the hypothetical call
        let c = c.into_rir()?;

        let f_axiom = self.build_function_axiom(i, c.clone())?;

        self.install_function_axiom(&c.ident, f_axiom)?;
        Ok(())
    }

    pub fn install_function_axiom(
        &mut self,
        ident: &str,
        f_axiom: Comp
    ) -> Result<(), String> {
        for (op_name, _, op) in self.ops.iter_mut() {
            if op_name == ident {
                match op {
                    Op::Fun(op) => {
                        op.axioms.push(f_axiom);
                        return Ok(())
                    }
                    op => return Err(format!(
                        "Function axiom can only be installed on Op::Fun, but {} is {:?}",
                        ident,
                        op,
                    )),
                }
            }
        }
        Err(format!(
            "Function axiom could not be installed: {} not found",
            ident,
        ))
    }

    pub fn reg_fn_declare(&mut self, f: ItemFn, is_total: bool) -> Result<(), String> {
        // Parse the signature into Rir types, and throw away
        // the body.
        let sig = RirFnSig::from_syn(f.sig)?;
        // Apply type aliases
        let sig = sig.expand_types(&self.type_aliases());

        self.reg_rir_declare(sig, is_total)
    }

    pub fn reg_rir_declare(
        &mut self,
        sig: RirFnSig,
        is_total: bool,
    ) -> Result<(), String> {
        // Assume type aliases are already applied
        let RirFnSig{ident, tas, inputs, output} = sig;
    
        // Throw away the input patterns, keep the types.
        let inputs: Vec<VType> =
            inputs.into_iter().map(|(_,t)| t).collect();
    
        // First, are any input thunks, making this a
        // higher-order function?
        let (op, extra_axioms) = if !inputs.iter().any(|i| i.contains_thunk()) {
            // If not, is the output bool?
            if output == VType::prop() {
                // Then this is a simple predicate.
                (Op::Symbol(PredSymbol{inputs}), Vec::new())
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
                    path: None,
                };
                let axiom = Self::relabs_axiom(
                    code.clone(),
                    inputs.clone(),
                    output.clone(),
                );
                let extra_axioms = if is_total {
                    vec![
                        constructions::totality_axiom(
                            code.clone(),
                            inputs.clone(),
                            output.clone(),
                        ).build(&mut Gen::new())
                    ]
                } else {
                    Vec::new()
                };
                (
                    Op::Fun(FunOp{
                        inputs,
                        output,
                        axioms: vec![axiom],
                    }),
                    extra_axioms,
                )
            }
        } else {
            // If this is a higher-order function, don't give
            // it the relational abstraction axiom. We will
            // rely on user-supplied axioms.
            if output == VType::prop() {
                todo!("Handle higher-order relations")
            } else {
                (Op::Fun(FunOp{
                    inputs,
                    output,
                    axioms: Vec::new(),
                }), Vec::new())
            }
        };
        self.ops.push((ident.clone(), tas.clone(), op));
        for axiom in extra_axioms {
            self.axioms.push(Axiom {
                tas: tas.clone(),
                inst_mode: InstMode::Code(ident.clone()),
                body: axiom,
            })
        }
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
        ident: SynIdent,
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

        self.sorts_insert(ident.to_string(), arity);
        Ok(())
    }

    pub fn reg_type_define(&mut self, i: ItemType) -> Result<(), String> {
        let ItemType{ident, ty, ..} = i;
        let right = VType::from_syn(*ty)?.expand_types(&self.type_aliases());
        self.add_alias(ident, right);
        Ok(())
    }
}
