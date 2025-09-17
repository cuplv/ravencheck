pub mod internal;

use crate::{
    parse_str_cbpv,
    Builder,
    Comp,
    Gen,
    Goal,
    Op,
    Quantifier,
    Sig,
    TypeContext,
    Val,
    VName,
    VType
};
use easy_smt::Response;

#[cfg(test)]
mod tests; 

#[derive(Clone)]
pub struct CheckedSig(pub Sig);

impl CheckedSig {
    pub fn check_goal(&self, goal: Goal) -> Result<(), String> {
        let Goal{title, tas, condition, should_be_valid} = goal;
        match query_negative_c(condition, self, tas) {
            Response::Unsat if should_be_valid => Ok(()),
            Response::Unsat =>
                Err(format!("Failed to falisfy '{}': solver did not find counterexample", title)),
            Response::Sat if !should_be_valid => Ok(()),
            Response::Sat =>
                Err(format!("Failed to verify '{}': solver found counterexample", title)),
            Response::Unknown if should_be_valid =>
                Err(format!("Failed to verify '{}': query could not be completed (sort cycle?)", title)),
            Response::Unknown =>
                Err(format!("Failed to falsify '{}': query could not be completed (sort cycle?)", title)),
        }
    }

    // pub fn assert_valid_comp(&self, c: Comp) -> Result<(), String> {
    //     match query_negative_c(c, self) {
    //         Response::Unsat => Ok(()),
    //         Response::Sat =>
    //             Err(format!("Solver found counterexample")),
    //         Response::Unknown =>
    //             Err(format!("Query could not be completed (sort cycle?)")),
    //     }
    // }
    // pub fn assert_invalid_comp(&self, c: Comp) -> Result<(), String> {
    //     match query_negative_c(c, self) {
    //         Response::Unsat =>
    //             Err(format!("Solver did not find counterexample")),
    //         Response::Sat => Ok(()),
    //         Response::Unknown =>
    //             Err(format!("Query could not be completed (sort cycle?)")),
    //     }
    // }
    pub fn assert_valid<T: ToString>(&self, s: T) {
        assert_valid_with(self, s)
    }
    pub fn assert_valid_t<T: ToString>(&self, title: &str, s: T) {
        assert_valid_with_t(self, title, s)
    }
    pub fn assert_invalid_t<T: ToString>(&self, title: &str, s: T) {
        assert_invalid_with_t(self, title, s)
    }
    pub fn assert_invalid<T: ToString>(&self, s: T) {
        assert_invalid_with(self, s)
    }
    pub fn assert_undecidable<T: ToString>(&self, s: T) {
        assert_unknown_with(self, s)
    }
    pub fn inner_sig(&self) -> &Sig {
        &self.0
    }

    pub fn empty() -> Self {
        let mut sig = Self(Sig::empty());
        sig.add_fun("implies", "|x:bool, y:bool| !x || y");
        sig
    }
    pub fn add_sort<S: ToString>(&mut self, s: S) -> VType {
        let t = VType::ui(s.to_string());
        self.0.add_sort(s);
        t
    }
    pub fn add_type_con<S: ToString>(&mut self, s: S, arity: usize) {
        self.0.add_type_con(s, arity);
    }
    pub fn add_alias<S1: ToString>(&mut self, s: S1, t: VType) -> VType {
        self.0.add_alias(s, t.clone());
        t
    }
    pub fn add_alias_from_string<S1: ToString, S2: ToString>(
        &mut self,
        alias: S1,
        ty_string: S2,
    ) {
        self.0.add_alias_from_string(alias, ty_string);
    }
    pub fn add_constant<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        sort: S2,
    ) {
        self.0.add_constant(name, sort)
    }
    pub fn add_relation<S1: ToString, S2: ToString, const N: usize>(
        &mut self,
        name: S1,
        inputs: [S2; N],
    ) {
        self.0.add_relation(name, inputs)
    }
    pub fn add_relation_t<S1: ToString, const N: usize>(
        &mut self,
        name: S1,
        inputs: [VType; N],
    ) {
        self.0.add_relation_t(name, inputs)
    }
    pub fn add_axiom<S1: ToString>(&mut self, axiom: S1) {
        self.0.add_axiom(axiom)
    }
    pub fn add_axiom2<const N1: usize, const N2: usize>(
        &mut self,
        def: &str,
        tas: [&str; N1],
        inst_rules: [(&str,Vec<&str>); N2],
    ) {
        self.0.add_axiom2(def, tas, inst_rules)
    }
    pub fn add_fun<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        def: S2,
    ) {
        self.add_fun_tas(name, [], None, def);
    }
    pub fn add_fun_tas<S1: ToString, S2: ToString, const N1: usize>(
        &mut self,
        name: S1,
        tas: [&str; N1],
        output: Option<&str>,
        def: S2,
    ) {
        let tas: Vec<String> = tas.iter().map(|s| s.to_string()).collect();
        // let inputs: Vec<VType> = inputs.into_iter().map(|i| {
        //     let t = VType::from_pat_type(i).expect("should be able to parse an input argument type as a VType");
        //     t.expand_aliases(&self.0.type_aliases)
        // }).collect();

        let mut unshadowed_aliases = self.0.type_aliases.clone();
        for a in tas.iter() {
            unshadowed_aliases.remove(a);
        }
        // let output: VType = VType::from_string(output)
        //     .expect("should be able to parse an input argument type as a VType")
        //     .expand_aliases(&unshadowed_aliases);

        let fun = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&unshadowed_aliases),
            Err(e) => panic!(
                "
Error in parsing definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };
        let tc = TypeContext::new_types(self.0.clone(), tas.clone());
        match fun.type_of(tc) {
            Ok(ct) => match ct.clone().unwrap_fun_v() {
                Some((_,out)) => match output {
                    Some(output) => {
                        let output: VType = VType::from_string(output)
                            .expect("should be able to parse an input argument type as a VType")
                            .expand_aliases(&unshadowed_aliases);
                        assert!(
                            output == out,
                            "
Error in type-checking definition of '{}':
output type should be '{}', but body had type '{}'",
                            name.to_string(),
                            output.render(),
                            out.render(),
                        );
                    }
                    None => {}
                }
                None => panic!(
                    "
Error in type-checking definition of \"{}\":
should have had a function type, instead had {:?}",
                    name.to_string(),
                    ct,
                ),
            }
            Err(e) => panic!(
                "
Error in type-checking definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        }
        self.0.ops.push((name.to_string(), tas, Op::Direct(fun)))
    }
    pub fn declare_op<S1: ToString, S3: ToString, const N1: usize, const N2: usize>(
        &mut self,
        name: S1,
        targs: [&str; N1],
        inputs: [&str; N2],
        output: S3,
    ) {
        self.0.declare_op(name, targs, inputs, output);
    }
    pub fn declare_const(&mut self, name: &str, output: &str) {
        self.0.declare_const(name, output);
    }
    pub fn add_annotation(&mut self, name: &str, body: &str) {
        self.0.add_annotation(name, body);
    }
    pub fn add_checked_annotation(&mut self, title: &str, name: &str, body: &str) {
        let mut potential_sig = self.0.clone();
        potential_sig.add_annotation(name, body);

        let (tas,op) = potential_sig
            .ops_map()
            .get(&name.to_string())
            .unwrap()
            .clone();

        let op = match op {
            Op::Rec(op) => op,
            _ => panic!(
                "Tried to add checked annotation to non-rec {}", name
            ),
        };

        // Add uninterpreted types for each type abstraction
        let mut v_sig = potential_sig.clone();
        let mut type_args = Vec::new();
        for t in &tas {
            v_sig.add_sort(t);
            type_args.push(VType::ui(t));
        }

        let mut gn = Gen::new();
        op.def.advance_gen(&mut gn);
        for a in &op.axioms {
            a.advance_gen(&mut gn);
        }
        let mut input_args: Vec<Val> = Vec::new();
        let mut q_sig: Vec<(VName, VType)> = Vec::new();
        for i in op.inputs {
            let x = gn.next();
            input_args.push(x.clone().val());
            q_sig.push((x, i.clone()))
        }
        let m =
            Builder::lift(op.def.clone())
            .apply_rt(input_args.clone())
            .seq_gen(move |x| {
                Builder::lift(op.axioms[op.axioms.len() - 1].clone())
                    .apply_rt(input_args)
                    .apply_rt(vec![x])
            })
            .quant(Quantifier::Forall, q_sig)
            .build(&mut gn);

        let v_sig = CheckedSig(v_sig);
        match query_negative_c(m, &v_sig, Vec::new()) {
            Response::Unsat => {},
            Response::Sat => {
                panic!(
                    "Annotation '{}' on recursive function '{}' is invalid",
                    title,
                    name.to_string(),
                )
            }
            Response::Unknown => {
                panic!(
                    "Verification of '{}' for '{}' cannot proceed",
                    title,
                    name.to_string(),
                )
            }
        }

        self.0 = potential_sig;
        
        // todo!("add_checked_annotation")
    }
    pub fn add_op_pred<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        def: S2,
    ) {
        self.0.add_op_pred(name, def)
    }
    pub fn add_op_fun<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        axiom: S2,
    ) {
        self.0.add_op_fun(name, axiom)
    }
    pub fn add_op_rec<S1: ToString + Clone, S2: ToString, S3: ToString>(
        &mut self,
        name: S1,
        axiom: S2,
        def: S3,
    ) {
        let mut potential_sig = self.0.clone();
        potential_sig.add_op_rec(
            name.clone(),
            axiom,
            def,
        );
        let op = potential_sig
            .ops_map()
            .get(&name.to_string())
            .unwrap()
            .clone();
        let op = match op {
            (_, Op::Rec(op)) => op,
            _ => panic!(),
        };
        let mut gn = Gen::new();
        op.def.advance_gen(&mut gn);
        for a in &op.axioms {
            a.advance_gen(&mut gn);
        }
        let mut input_args: Vec<Val> = Vec::new();
        let mut q_sig: Vec<(VName, VType)> = Vec::new();
        for i in op.inputs {
            let x = gn.next();
            input_args.push(x.clone().val());
            q_sig.push((x, i.clone()))
        }
        let m =
            Builder::lift(op.def.clone())
            .apply_rt(input_args.clone())
            .seq_gen(move |x| {
                Builder::lift(op.axioms[0].clone())
                    .apply_rt(input_args)
                    .apply_rt(vec![x])
            })
            .quant(Quantifier::Forall, q_sig)
            .build(&mut gn);
        // Build assertion body: for all inputs, apply the definition to
        // get the output, and then check that the inputs and output
        // are related by the annotation.
        self.0 = potential_sig;
        match query_negative_c(m, &self, Vec::new()) {
            Response::Unsat => {},
            Response::Sat => {
                panic!(
                    "The annotation on recursive function \"{}\" is invalid",
                    name.clone().to_string(),
                )
            }
            Response::Unknown => {
                panic!(
                    "Verification of \"{}\" cannot proceed",
                    name.clone().to_string(),
                )
            }
        }
        // self.0.add_op_rec(name, axiom, def, term_arg, term_relation)
    }

    pub fn define_op_rec<S1: ToString + Clone, S2: ToString, S3: ToString, S4: ToString, const N1: usize, const N2: usize>(
        &mut self,
        name: S1,
        tas: [&str; N1],
        inputs: [S2; N2],
        output: S3,
        def: S4,
    ) {
        self.0.define_op_rec(name, tas, inputs, output, def);

//         let tas: Vec<String> = tas.iter().map(|s| s.to_string()).collect();

//         let mut unshadowed_aliases = self.0.type_aliases.clone();
//         for a in tas.iter() {
//             unshadowed_aliases.remove(a);
//         }

//         let def = match parse_str_cbpv(&def.to_string()) {
//             Ok(m) => m.expand_types(&unshadowed_aliases),
//             Err(e) => panic!(
//                 "
// Error in parsing definition of \"{}\": {:?}",
//                 name.to_string(),
//                 e,
//             ),
//         };
//         let self_op = Op::Fun(FunOp{
//             inputs: inputs.clone()
//         });

//         let tc = TypeContext::new_types(self.0.clone(), tas.clone());
//         match def.type_of(tc) {
//             Ok(ct) => match ct.clone().unwrap_fun_v() {
//                 Some(_) => {},
//                 None => panic!(
//                     "
// Error in type-checking definition of \"{}\":
// should have had a function type, instead had {:?}",
//                     name.to_string(),
//                     ct,
//                 ),
//             }
//             Err(e) => panic!(
//                 "
// Error in type-checking definition of \"{}\": {:?}",
//                 name.to_string(),
//                 e,
//             ),
//         }

    }
}


fn query_negative<T: ToString>(s: T, sig: &CheckedSig) -> Response {
    match parse_str_cbpv(&s.to_string()) {
        Ok(c) => query_negative_c(c, sig, Vec::new()),
        Err(e) => panic!("Parse error: {}", e),
    }
}

fn query_negative_c(c: Comp, sig: &CheckedSig, tas: Vec<String>) -> Response {
    let mut sig = sig.clone();
    // Declare all type abstraction arguments as zero-arity
    // uninterpreted sorts.
    for s in tas {
        sig.0.sorts.insert(s, 0);
    }
    let mut p = match c.as_prop(sig.inner_sig()) {
        Ok(p) => p,
        Err(e) => panic!("{}", e),
    };
    println!("Checking {} cases...", p.cases.len());
    assert!(p.is_single_case(), "Should only be single-case props so far.");
    p.negate(sig.inner_sig());
    for (name, case) in p.cases {
        let g = sig.inner_sig().sort_graph_combined(&case);
        let cycles = g.get_cycles();
        if cycles.len() > 0 {
            println!("Sort cycles detected in case [{}]:", name);
            for c in cycles {
                if c.len() == 1 {
                    println!("=> self-loop on {:?}", c[0]);
                } else {
                    println!("=> {:?}", c);
                }
            }
            println!("Query is undecidable due to sort cycles.");
            return Response::Unknown
        }
        match internal::check_sat_of_normal(&case, sig.inner_sig()).unwrap() {
            Response::Sat => {
                println!("Got SAT for case [{}]", name);
                return Response::Sat
            }
            Response::Unsat => {},
            Response::Unknown => {
                println!("Got UNKNOWN for case [{}]", name);
                return Response::Unknown
            }
        }
    }

    // If we made it here, the overall answer is UNSAT.
    Response::Unsat
}

pub fn assert_valid_with<T: ToString>(sig: &CheckedSig, s: T) {
    match query_negative(s, sig) {
        Response::Unsat => {},
        Response::Sat => panic!("
verification conditions are not valid, counterexample was found"
        ),
        Response::Unknown => panic!("
verification could not be completed (sort cycle?)"
        ),
    }
    // assert_eq!(query_negative(s, sig), Response::Unsat);
}
pub fn assert_valid_with_t<T: ToString>(sig: &CheckedSig, title: &str, s: T) {
    match query_negative(s, sig) {
        Response::Unsat => {},
        Response::Sat => panic!("verification goal {} is invalid", title),
        Response::Unknown => panic!("verification goal {} could not be checked (sort cycle?)", title),
    }
    // assert_eq!(query_negative(s, sig), Response::Unsat);
}

pub fn assert_invalid_with_t<T: ToString>(sig: &CheckedSig, title: &str, s: T) {
    match query_negative(s, sig) {
        Response::Unsat => panic!("falsification goal {} is actually valid", title),
        Response::Sat => {},
        Response::Unknown => panic!("falsification goal {} could not be checked (sort cycle?)", title),
    }
}

pub fn assert_invalid_with<T: ToString>(sig: &CheckedSig, s: T) {
    assert_eq!(query_negative(s, sig), Response::Sat);
}

pub fn assert_unknown_with<T: ToString>(sig: &CheckedSig, s: T) {
    assert_eq!(query_negative(s, sig), Response::Unknown);
}
