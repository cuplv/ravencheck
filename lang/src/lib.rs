mod builder;
pub use builder::Builder;
mod cbpv;
pub use cbpv::{
    Binder1,
    BinderN,
    CaseName,
    Cases,
    Comp,
    HypotheticalCall,
    Literal,
    LogOpN,
    OpMode,
    Pattern,
    Quantifier,
    Val,
};
mod depth;
pub mod epr_check;
mod expand_funs;
mod expand_types;
mod neg_normal_form;
mod negate;
mod partial_eval;
pub mod prop;
pub use prop::Prop;
mod rebuild;
pub use rebuild::Rebuild;
mod register;
mod relevant;
mod rename;
mod sig;
pub use sig::{
    Axiom,
    BType,
    CType,
    FunOp,
    InstRule,
    PredOp,
    PredSymbol,
    Op,
    OpCode,
    RecOp,
    Sig,
    VType
};
mod smt;
pub use smt::CheckedSig;
mod substitute;
mod type_check;
pub use type_check::TypeContext;
mod vname;
pub use vname::VName;
mod gen;
pub use gen::Gen;

mod syn_to_cbpv;
pub use syn_to_cbpv::{
    InstRuleSyntax,
    HypotheticalCallSyntax,
    RirFn,
    RirFnSig,
    syn_to_builder,
    block_to_builder,
};

pub struct Goal {
    pub title: String,
    pub tas: Vec<String>,
    pub condition: Comp,
    pub should_be_valid: bool,
}

pub fn parse_str_syn<T: syn::parse::Parse>(input: &str) -> syn::Result<T> {
    syn::parse_str(input)
}

pub fn parse_str_cbpv(input: &str) -> syn::Result<cbpv::Comp> {
    
    match syn::parse_str(input) {
        Ok(expr) => match syn_to_builder(expr) {
            Ok(b) => {
                let mut gen = Gen::new();
                Ok(b.build(&mut gen))
            }
            Err(e) => panic!("syn_to_builder error: {}", e),
        }
        Err(err) => Err(err),
    }
}

impl Comp {
    pub fn type_check_prop(&self, sig: &Sig) {
        match self.type_check(&CType::return_prop(), sig) {
            Ok(()) => {},
            Err(e) => panic!("Type error: {}", e),
        }
    }
    pub fn normal_form(self, sig: &Sig) -> Cases {
        let mut gen = self.get_gen();
        self.normal_form_x(sig, &mut gen, CaseName::root())
    }
    pub fn normal_form_single_case(
        self,
        sig: &Sig,
        gen: &mut Gen,
    ) -> Self {
        let mut cases = self.normal_form_x(sig, gen, CaseName::root());
        assert!(
            cases.len() == 1,
            "normal_form_single_case should only be called on comps that produce 1 case, but comp produced {} cases",
            cases.len(),
        );
        cases.pop().unwrap().1
    }
    pub fn normal_form_x(
        self,
        sig: &Sig,
        gen: &mut Gen,
        starting_name: CaseName,
    ) -> Cases {
        let cases_pe = self.partial_eval(sig, gen, starting_name);
        // println!("got {} cases from partial_eval", cases_pe.len());

        let mut cases_nnf = Vec::new();
        for (name,comp) in cases_pe.into_iter() {
            cases_nnf.push((name, comp.neg_normal_form(sig,gen)));
        };

        let mut cases_exp = Vec::new();
        for (name,comp) in cases_nnf.into_iter() {
            cases_exp.push((name, comp.expand_funs(sig,gen,Vec::new())));
        };

        // println!("normal_form_x passing on {} cases", cases_exp.len());
        cases_exp
    }
}

impl Sig {
    pub fn get_applied_op(
        &self,
        oc: &OpCode,
    ) -> Result<Op, String> {
        let name = &oc.ident;
        let targs = &oc.types;
        match self.get_op(name) {
            Some((tas, op)) if targs.len() == tas.len() => {
                Ok(op.clone().expand_types_from_call(targs, tas).unwrap())
            }
            Some((tas, _)) => {
                let targs_s: Vec<String> = targs.iter().map(|t| t.render()).collect();
                Err(format!("Wrong number of type args ({:?}) for op '{}', expected {:?}", targs_s, name, tas))
            }
            None => Err(format!("Op '{}' is undefined", name)),
        }
    }

    pub fn add_axiom<S1: ToString>(
        &mut self,
        def: S1,
    ) {
        let tas: [String; 0] = [];
        let inst_rules: [(String,Vec<String>); 0] = [];
        self.add_axiom2(def, tas, inst_rules);
    }

    pub fn add_axiom2<S1: ToString, S2: ToString, S3: ToString, const N1: usize, const N2: usize>(
        &mut self,
        def: S1,
        tas: [S2; N1],
        inst_rules: [(S3,Vec<S3>); N2],
    ) {
        let mut tas_parsed = Vec::new();
        for t in &tas {
            tas_parsed.push(t.to_string());
        }

        let mut inst_rules_parsed = Vec::new();
        for (a,bs) in &inst_rules {
            let a = BType::from_string(a.to_string()).unwrap();
            let bs = bs.iter().map(|b| {
                VType::from_string(b.to_string()).unwrap()
            }).collect();
            inst_rules_parsed.push(InstRule{left: a, right: bs});
        }

        let axiom = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&self.type_aliases),
            Err(e) => panic!(
                "
Error in parsing axiom \"{}\": {:?}",
                def.to_string(),
                e,
            ),
        };
        match axiom.type_of(TypeContext::new_types(self.clone(), tas_parsed.clone())) {
            Ok(t) => {
                if t != CType::return_prop() {
                    panic!(
                        "
Axiom \"{}\" has type {:?}, must have type \"bool\"
",
                        def.to_string(),
                        t,
                    )
                }
            }
            Err(e) => panic!(
                "
Type error in axiom \"{}\": {:?}",
                def.to_string(),
                e,
            ),
        }

        // let mut cases = axiom.normal_form(self);
        // assert!(
        //     cases.len() == 1,
        //     "Axiom comp should have 1 case, had {} cases instead",
        //     cases.len(),
        // );
        let axiom_a = Axiom {
            tas: tas.into_iter().map(|s| s.to_string()).collect(),
            inst_rules: inst_rules_parsed,
            // body: cases.pop().unwrap().1,
            body: axiom,
        };
        self.axioms.push(axiom_a);
    }

    pub fn add_alias_from_string<S1: ToString, S2: ToString>(
        &mut self,
        alias: S1,
        ty_string: S2,
    ) {
        let ty = VType::from_syn(
            syn::parse_str(&ty_string.to_string()).unwrap()
        ).unwrap();
        let ty2 = ty.clone().expand_aliases(&self.type_aliases);
        println!(
            "Adding alias: {} = {} => {}",
            alias.to_string(),
            ty.render(),
            ty2.render(),
        );
        self.add_alias(alias, ty2);
    }

    pub fn add_annotation<S1: ToString, S2: ToString>(
        &mut self,
        op_name: S1,
        def: S2,
    ) {
        let mut found = false;

        // Parse the comp from def
        let c = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&self.type_aliases),
            Err(e) => panic!(
                "
Error parsing annotation: {}",
                e,
            ),
        };

        let sig_clone = self.clone();
        for (name,tas,op) in self.ops.iter_mut() {
            if &op_name.to_string() == name {
                found = true;
                let tc = TypeContext::new_types(sig_clone.clone(), tas.clone());
                match op {
                    Op::Fun(op) => {
                        // Check the type of c against the inputs and
                        // outputs of op.
                        
                        match c.type_check_r(&op.annotation_type(), tc) {
                            Ok(()) => {},
                            Err(e) =>
                                panic!("Type error in annotation def: {}", e),
                        }

                        op.axioms.push(c.clone());
                    }
                    Op::Rec(op) => {
                        // Check the type of c against the inputs and
                        // outputs of op.
                        match c.type_check_r(&op.annotation_type(), tc) {
                            Ok(()) => {},
                            Err(e) =>
                                panic!("Type error in annotation def: {}", e),
                        }

                        op.axioms.push(c.clone());
                    }                        
                    _ => panic!("Annotation added to '{}', which is a type of operation other than function or rec.", op_name.to_string()),
                }
            }
        }

        assert!(
            found,
            "No function called '{}' has been declared",
            op_name.to_string(),
        );
    }
    pub fn add_op_pred<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        def: S2,
    ) {
        let axiom = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&self.type_aliases),
            Err(e) => panic!(
                "
Error in parsing def of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };
        let inputs = match axiom.type_of(TypeContext::new(self.clone())) {
            Ok(t) => match t.unwrap_fun_v() {
                Some((inputs, output)) => {
                    assert!(
                        output == VType::prop(),
                        "Output type of \"{}\" must be \"bool\"",
                        name.to_string(),
                    );
                    inputs
                }
                None => panic!()
            }
            Err(e) => panic!(
                "
Type error in def of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };
        let op = Op::Pred(PredOp{
            inputs,
            axioms: vec![axiom],
        });
        self.ops.push((name.to_string(), Vec::new(), op));
    }

    fn relabs_axiom(code: OpCode, inputs: Vec<VType>, output: VType) -> Comp {
        let rel_abs = Val::OpCode(OpMode::RelAbs, code);

        // let output_clone = output.clone();
        Builder::ret_thunk(
            Builder::fun_many_gen(inputs, |in_xs| {
                Builder::ret_thunk(
                    Builder::fun_gen(output, |out_x| {
                        let mut args = in_xs;
                        args.push(out_x);
                        Builder::force(rel_abs).apply_v(args)
                    })
                )
            })
        ).build(&mut Gen::new())
    }

    pub fn declare_op_parsed(&mut self, name: String, targs: Vec<String>, inputs: Vec<VType>, output: VType) {
        let op = if !inputs.iter().any(|i| i.contains_thunk()) {
            if output == VType::prop() {
                Op::Symbol(PredSymbol{inputs})
            } else {
                // Add an annotation that links the op to its
                // relational abstraction.

                let code_args = targs.iter().cloned().map(VType::ui).collect();
                let code = OpCode { ident: name.to_string(), types: code_args };
                let axiom = Self::relabs_axiom(
                    code,
                    inputs.clone(),
                    output.clone()
                );
                Op::Fun(FunOp{
                    inputs,
                    output,
                    axioms: vec![axiom],
                })
            }
        } else {
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
        self.ops.push((name.to_string(), targs, op));
    }

    pub fn declare_const(&mut self, name: &str, output: &str) {
        self.add_constant(name, output);
    }

    pub fn declare_op<S1: ToString, S2: ToString, S3: ToString, S4: ToString, const N1: usize, const N2: usize>(
        &mut self,
        name: S1,
        targs: [S2; N1],
        inputs: [S3; N2],
        output: S4,
    ) {
        let targs: Vec<String> =
            targs.into_iter().map(|s| s.to_string()).collect();

        let inputs: Vec<VType> = inputs.into_iter().map(|i| {
            let t = VType::from_pat_type(i).expect("should be able to parse an input argument type as a VType");
            t.expand_aliases(&self.type_aliases)
        }).collect();
        let output: VType = VType::from_string(output)
            .expect("should be able to parse an input argument type as a VType")
            .expand_aliases(&self.type_aliases);

        self.declare_op_parsed(name.to_string(), targs, inputs, output)
    }

    pub fn define_op_rec<S1: ToString + Clone, S2: ToString, S3: ToString, S4: ToString, const N1: usize, const N2: usize>(
        &mut self,
        name: S1,
        tas: [&str; N1],
        inputs: [S2; N2],
        output: S3,
        def: S4,
    ) {
        // First, parse everything
        let tas: Vec<String> =
            tas.into_iter().map(|s| s.to_string()).collect();
        let inputs: Vec<VType> = inputs.into_iter().map(|i| {
            let t = VType::from_pat_type(i).expect("should be able to parse an input argument type as a VType");
            t.expand_aliases(&self.type_aliases)
        }).collect();
        let output: VType = VType::from_string(output)
            .expect("should be able to parse an input argument type as a VType")
            .expand_aliases(&self.type_aliases);

        let mut unshadowed_aliases = self.type_aliases.clone();
        for a in tas.iter() {
            unshadowed_aliases.remove(a);
        }

        let def = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&unshadowed_aliases),
            Err(e) => panic!(
                "
Error in parsing definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };

        // Need to typecheck def against intputs+output, while letting
        // 'tas' shadow any aliases, and assuming that the recursive
        // call already has the given type.

        // Define a copy of the sig in which recursive call is an
        // uninterpreted function.
        let mut rec_sig = self.clone();
        rec_sig.declare_op_parsed(name.to_string(), tas.clone(), inputs.clone(), output.clone());

        // Type-check, using rec_sig, against inputs+outputs
        let d_type =
            CType::Return(
                VType::Thunk(
                    Box::new(
                        CType::fun(
                            inputs.clone(),
                            CType::Return(output.clone())
                        )
                    )
                )
            );
        let tc = TypeContext::new_types(rec_sig, tas.clone());
        match def.type_check_r(&d_type, tc) {
            Ok(()) => {},
            Err(e) => panic!(
                "
Error in type-checking definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        }

        let code_args = tas.iter().cloned().map(VType::ui).collect();
        let code = OpCode { ident: name.to_string(), types: code_args };
        let axiom = Self::relabs_axiom(
            code,
            inputs.clone(),
            output.clone()
        );
        let op = Op::Rec(RecOp{
            inputs,
            output,
            axioms: vec![axiom],
            def,
        });
        self.ops.push((name.to_string(), tas, op));
        // todo!("define_op_rec");
    }

    pub fn add_op_fun<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        axiom: S2,
    ) {
        let axiom = match parse_str_cbpv(&axiom.to_string()) {
            Ok(m) => m.expand_types(&self.type_aliases),
            Err(e) => panic!(
                "
Error in parsing axiom of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };
        let (inputs, rest) = match axiom.type_of(TypeContext::new(self.clone())) {
            Ok(t) => match t.unwrap_fun_v() {
                Some(in_rest) => in_rest,
                None => panic!()
            }
            Err(e) => panic!(
                "
Type error in axiom of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };

        let fun_output = match rest.unwrap_fun_v() {
            Some((inputs, output)) => {
                assert!(
                    output == VType::prop(),
                    "Body type of \"{}\" def must be \"bool\"",
                    name.to_string(),
                );
                assert!(
                    inputs.len() == 1,
                    "Def of \"{}\" must have one output argument",
                    name.to_string(),
                );
                inputs[0].clone()
            }
            None => panic!(
                "Def of \"{}\" is malformed, should be function of form |inputs| |output| {{ axiom body }}",
                name.to_string(),
            ),
        };

        let op = Op::Fun(FunOp{
            inputs,
            output: fun_output,
            axioms: vec![axiom],
        });
        self.ops.push((name.to_string(), Vec::new(), op));
    }

    pub fn add_op_rec<S1: ToString, S2: ToString, S3: ToString>(
        &mut self,
        name: S1,
        axiom: S2,
        def: S3,
    ) {
        let axiom = match parse_str_cbpv(&axiom.to_string()) {
            Ok(m) => m.expand_types(&self.type_aliases),
            Err(e) => panic!(
                "
Error in parsing axiom of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };
        let (inputs, rest) = match axiom.type_of(TypeContext::new(self.clone())) {
            Ok(t) => match t.unwrap_fun_v() {
                Some(in_rest) => in_rest,
                None => panic!()
            }
            Err(e) => panic!(
                "
Type error in axiom of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };

        let fun_output = match rest.unwrap_fun_v() {
            Some((inputs, output)) => {
                assert!(
                    output == VType::prop(),
                    "Body type of \"{}\" annotation must be \"bool\"",
                    name.to_string(),
                );
                assert!(
                    inputs.len() == 1,
                    "Annotation of \"{}\" must have one output argument",
                    name.to_string(),
                );
                inputs[0].clone()
            }
            None => panic!(
                "Annotation of \"{}\" is malformed, should be function of form |inputs| |output| {{ annotation body }}",
                name.to_string(),
            ),
        };

        let def = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&self.type_aliases),
            Err(e) => panic!(
                "
Error in parsing definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };

        let self_op = Op::Fun(FunOp{
            inputs: inputs.clone(),
            output: fun_output.clone(),
            axioms: vec![axiom.clone()],
        });
        let mut self_sig = self.clone();
        self_sig.ops.push((name.to_string(), Vec::new(), self_op));

        match def.type_of(TypeContext::new(self_sig)) {
            Ok(t) => {
                let expected =
                    CType::Return(
                        VType::fun_v(inputs.clone(), fun_output.clone())
                    );
                if t != expected {
                    panic!(
                        "
{:?}'s definition type {:?} does not match annotation type {:?}",
                        name.to_string(),
                        t,
                        expected,
                    );
                }
            }
            Err(e) => panic!(
                "
Type error in definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        }

        let op = Op::Rec(RecOp{
            inputs,
            output: fun_output,
            axioms: vec![axiom],
            def,
        });
        self.ops.push((name.to_string(), Vec::new(), op));

    }
}
