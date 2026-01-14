mod rir;
pub use rir::ast::{
    Binder1,
    BinderN,
    CaseName,
    Cases,
    Comp,
    HypotheticalCall,
    Literal,
    LogOpN,
    MatchArm,
    OpMode,
    Pattern,
    Quantifier,
    Val,
};
pub use rir::builder::Builder;
mod eliminate_match;
pub mod epr_check;
pub use epr_check::{Cycle, render_cycle};
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
    InstMode,
    InstRule,
    PredOp,
    PredSymbol,
    Op,
    OpCode,
    RecOp,
    Sig,
    TypeDef,
    VType,
};
mod smt;
pub use smt::CheckedSig;
pub use smt::solver::SolverConfig;
mod substitute;
mod type_check;
pub use type_check::TypeContext;
mod utility;
pub use rir::ident::Ident;
pub use rir::igen::IGen;
mod tag_recursive;

pub use rir::from_syn::{
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

pub fn parse_str_cbpv(input: &str) -> syn::Result<Comp> {
    
    match syn::parse_str(input) {
        Ok(expr) => match syn_to_builder(expr) {
            Ok(b) => {
                let mut igen = IGen::new();
                Ok(b.build_with(&mut igen))
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
        let mut igen = self.get_igen();
        self.normal_form_x(sig, &mut igen, CaseName::root())
    }
    pub fn normal_form_single_case(
        self,
        sig: &Sig,
        igen: &mut IGen,
    ) -> Self {
        let mut cases = self.normal_form_x(sig, igen, CaseName::root());
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
        igen: &mut IGen,
        starting_name: CaseName,
    ) -> Cases {
        // Partial evaluation
        let cases = self.partial_eval(sig, igen, starting_name);
        // println!("got {} cases from partial_eval", cases_pe.len());

        // Add recursion guards if defined
        let cases = match &sig.recs {
            Some(recs) => cases.into_iter().map(|(name,comp)| {
                // println!("Adding recursion guards for {:?}", &recs);
                let comp = comp.tag_recursive(sig, igen, recs);
                (name, comp)
            }).collect::<Vec<_>>(),
            None => cases,
        };

        // Match elimination
        let cases = cases.into_iter().map(|(name,comp)| {
            let comp = comp.eliminate_match(sig,igen);
            // println!("After match elimination: {:?}", comp);
            (name, comp)
        }).collect::<Vec<_>>();

        // Negation normal form (NNF)
        let cases = cases.into_iter().map(|(name,comp)| {
            (name, comp.neg_normal_form(sig,igen))
        }).collect::<Vec<_>>();

        // Function expansion
        let cases = cases.into_iter().map(|(name,comp)| {
            (name, comp.expand_funs(sig, igen, Vec::new()))
        }).collect::<Vec<_>>();

        // println!("normal_form_x passing on {} cases", cases_exp.len());
        cases
    }
}

#[derive(Debug)]
pub enum Oc {
    Op(Op),
    Con(Vec<VType>),
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

    pub fn get_applied_op_or_con(
        &self,
        oc: &OpCode,
    ) -> Result<Oc, String> {
        match &oc.path {
            Some(path) => match self.type_defs.get(path) {
                Some((tas, TypeDef::Enum(vs))) if oc.types.len() == tas.len() => {
                    let inputs = match vs.get(&oc.ident) {
                        Some(ts) => ts
                            .iter()
                            .map(|t| {
                                t.clone().expand_types_from_call(
                                    &oc.types,
                                    tas
                                )
                            })
                            .collect::<Result<Vec<_>,_>>(),
                        None => Err(format!(
                            "Enum {} does not have a variant {}",
                            path, oc.ident
                        )),
                    }?;
                    Ok(Oc::Con(inputs))
                }
                Some((tas, _)) => Err(format!(
                    "Enum {} should have {} type args, but got {}",
                    path, tas.len(), oc.types.len()
                )),
                None => Err(format!(
                    "Enum {} is not defined (did you declare it instead?)",
                    path,
                )),
            }
            None => match self.get_applied_op(oc) {
                Ok(op) => Ok(Oc::Op(op)),
                Err(e) => Err(e),
            }
        }
    }

    pub fn get_con_codes_with_inputs_btype(
        &self,
        t: &BType,
    ) -> Option<Vec<(OpCode, Vec<VType>)>> {
        match t {
            BType::UI(path, types) =>
                self.get_con_codes_with_inputs(path, types.clone()),
            _ => None,
        }
    }
    pub fn get_con_codes_with_inputs(
        &self,
        path: &str,
        types: Vec<VType>,
    ) -> Option<Vec<(OpCode, Vec<VType>)>> {
        match self.type_defs.get(path) {
            Some((tas, def)) => match def {
                TypeDef::Enum(vars) => {
                    let mut out = Vec::new();
                    for (ident, inputs) in vars {
                        let inputs = inputs.clone().into_iter().map(|i| i.expand_types_from_call(&types, &tas).unwrap()).collect();
                        let code = OpCode{
                            ident: ident.clone(),
                            types: types.clone(),
                            path: Some(path.to_string()),
                        };
                        out.push((code, inputs));
                            
                    }
                    Some(out)
                }
                _ => None,
            }
            _ => None,
        }
        
    }

    pub fn opcode_type(
        &self,
        oc: &OpCode,
        tas: Vec<String>,
    ) -> Result<VType, String> {
        match self.get_applied_op_or_con(oc) {
            Ok(Oc::Con(inputs)) => {
                let path = oc.path.clone().unwrap();
                let t = if inputs.len() == 0 {
                    // If the constructor's type has zero args, then
                    // we report this as a constant of the enum type.
                    VType::ui_args(path, oc.types.clone())
                } else {
                    // Otherwise, it's a function that produces a
                    // value of the enum type.
                    VType::fun_v(
                        inputs,
                        VType::ui_args(path, oc.types.clone()),
                    )
                };
                Ok(t)
            }
            Ok(Oc::Op(op)) => match op {
                Op::Const(op) => {
                    return Ok(op.vtype)
                }
                Op::Direct(m) => {
                    match m.type_of(TypeContext::new_types(self.clone(), tas))? {
                        CType::Return(t) => return Ok(t),
                        _ => return Err(format!(
                            "signature function \"{}\" did not have a computation type",
                            oc,
                        )),
                    }
                }
                Op::Fun(op) => {
                    return Ok(VType::fun_v(
                        op.inputs,
                        op.output,
                    ))
                },
                Op::Pred(op) => {
                    return Ok(VType::fun_v(
                        op.inputs,
                        VType::prop(),
                    ))
                },
                Op::Rec(op) => {
                    return Ok(VType::fun_v(
                        op.inputs,
                        op.output,
                    ))
                }
                Op::Symbol(op) => {
                    return Ok(VType::fun_v(
                        op.inputs,
                        VType::prop(),
                    ))
                }
            }
            Err(e) => Err(e),
        }
    }

    pub fn opcode_relabs_type(
        &self,
        oc: &OpCode,
        _tas: Vec<String>,
    ) -> Result<VType, String> {
        match self.get_applied_op_or_con(oc) {
            Ok(Oc::Con(inputs)) => {
                let path = oc.path.clone().unwrap();
                if inputs.len() > 0 {
                    let mut rel_inputs = Vec::new();
                    for i in inputs {
                        rel_inputs.push(i.clone());
                    }
                    rel_inputs.push(VType::ui_args(path, oc.types.clone()));
                    Ok(VType::fun_v(rel_inputs, VType::prop()))
                } else {
                    Err(format!("Zero-arg constructors (such as {}) have no defined RelAbs type.", oc.ident))
                }
            }
            Ok(Oc::Op(op)) => match op {
                Op::Fun(op) => {
                    let mut rel_inputs = Vec::new();
                    for i in op.inputs {
                        rel_inputs.push(i.clone());
                    }
                    rel_inputs.push(op.output.clone());
                    return Ok(VType::fun_v(
                        rel_inputs,
                        VType::prop(),
                    ))
                }
                _ => Err(format!("Only declared functions, recursive functions, and constructors have a RelAbs type; none is defined for {}", oc.ident)),
            }
            Err(e) => Err(e),
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
            Ok(m) => m.expand_types(&self.type_aliases()),
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
            inst_mode: InstMode::Rules(inst_rules_parsed),
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
        let ty2 = ty.clone().expand_aliases(&self.type_aliases());
        // println!(
        //     "Adding alias: {} = {} => {}",
        //     alias.to_string(),
        //     ty.render(),
        //     ty2.render(),
        // );
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
            Ok(m) => m.expand_types(&self.type_aliases()),
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
            Ok(m) => m.expand_types(&self.type_aliases()),
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
            Builder::fun_many_igen(inputs, |in_xs| {
                Builder::ret_thunk(
                    Builder::fun_igen(output, |out_x| {
                        let mut args = in_xs;
                        args.push(out_x);
                        Builder::force(rel_abs).apply_v(args)
                    })
                )
            })
        ).build_with(&mut IGen::new())
    }

    pub fn declare_op_parsed(&mut self, name: String, targs: Vec<String>, inputs: Vec<VType>, output: VType) {
        let op = if !inputs.iter().any(|i| i.contains_thunk()) {
            if output == VType::prop() {
                Op::Symbol(PredSymbol{inputs})
            } else {
                // Add an annotation that links the op to its
                // relational abstraction.

                let code_args = targs.iter().cloned().map(VType::ui).collect();
                let code = OpCode { ident: name.to_string(), types: code_args, path: None };
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
            t.expand_aliases(&self.type_aliases())
        }).collect();
        let output: VType = VType::from_string(output)
            .expect("should be able to parse an input argument type as a VType")
            .expand_aliases(&self.type_aliases());

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
            t.expand_aliases(&self.type_aliases())
        }).collect();
        let output: VType = VType::from_string(output)
            .expect("should be able to parse an input argument type as a VType")
            .expand_aliases(&self.type_aliases());

        let mut unshadowed_aliases = self.type_aliases();
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
        let code = OpCode { ident: name.to_string(), types: code_args, path: None };
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
            Ok(m) => m.expand_types(&self.type_aliases()),
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
            Ok(m) => m.expand_types(&self.type_aliases()),
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
            Ok(m) => m.expand_types(&self.type_aliases()),
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
