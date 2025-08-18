pub mod internal;

use crate::{
    parse_str_cbpv,
    Builder,
    Comp,
    Gen,
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

pub struct CheckedSig(Sig);

impl CheckedSig {
    pub fn assert_valid<T: ToString>(&self, s: T) {
        assert_valid_with(self, s)
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
    pub fn add_alias<S1: ToString>(&mut self, s: S1, t: VType) -> VType {
        self.0.add_alias(s, t.clone());
        t
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
    pub fn add_fun<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        def: S2,
    ) {
        let fun = match parse_str_cbpv(&def.to_string()) {
            Ok(m) => m.expand_types(&self.0),
            Err(e) => panic!(
                "
Error in parsing definition of \"{}\": {:?}",
                name.to_string(),
                e,
            ),
        };
        match fun.type_of(TypeContext::new(self.0.clone())) {
            Ok(ct) => match ct.clone().unwrap_fun_v() {
                Some(_) => {},
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
        self.0.ops.push((name.to_string(), Op::Direct(fun)))
    }
    pub fn declare_op<S1: ToString, S3: ToString, const N: usize>(
        &mut self,
        name: S1,
        inputs: [&str; N],
        output: S3,
    ) {
        self.0.declare_op(name, inputs, output);
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
            Op::Rec(op) => op,
            _ => panic!(),
        };
        let mut gn = Gen::new();
        op.def.advance_gen(&mut gn);
        op.axiom.advance_gen(&mut gn);
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
                Builder::lift(op.axiom.clone())
                    .apply_rt(input_args)
                    .apply_rt(vec![x])
            })
            .quant(Quantifier::Forall, q_sig)
            .build(&mut gn);
        // Build assertion body: for all inputs, apply the definition to
        // get the output, and then check that the inputs and output
        // are related by the annotation.
        self.0 = potential_sig;
        match query_negative_c(m, &self) {
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
}


fn query_negative<T: ToString>(s: T, sig: &CheckedSig) -> Response {
    match parse_str_cbpv(&s.to_string()) {
        Ok(c) => query_negative_c(c, sig),
        Err(e) => panic!("Parse error: {}", e),
    }
}

fn query_negative_c(c: Comp, sig: &CheckedSig) -> Response {
    // let mut p = match Prop::parse(&s.to_string(), sig.inner_sig()) {
    //     Ok(p) => p,
    //     Err(e) => panic!("{}", e),
    // };
    let mut p = match c.as_prop(sig.inner_sig()) {
        Ok(p) => p,
        Err(e) => panic!("{}", e),
    };
    println!("Checking {} cases...", p.cases.len());
    assert!(p.is_single_case(), "Should only be single-case props so far.");
    p.negate(sig.inner_sig());
    let sig_graph = sig.inner_sig().sort_graph();
    for (name, case) in p.cases {
        let mut g = sig_graph.clone();
        g.append(case.sort_graph());
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
    assert_eq!(query_negative(s, sig), Response::Unsat);
}

pub fn assert_invalid_with<T: ToString>(sig: &CheckedSig, s: T) {
    assert_eq!(query_negative(s, sig), Response::Sat);
}

pub fn assert_unknown_with<T: ToString>(sig: &CheckedSig, s: T) {
    assert_eq!(query_negative(s, sig), Response::Unknown);
}
