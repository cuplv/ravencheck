use crate::{
    Binder1,
    BinderN,
    Builder,
    CaseName,
    Comp,
    Gen,
    Literal,
    LogOpN,
    Op,
    Pattern,
    Rebuild,
    Sig,
    SName,
    Val,
    VName,
    VType,
};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Frame {
    Seq(Vec<Pattern>, Comp),
    Args(Vec<Val>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Stack(Vec<Frame>);

impl Stack {
    pub fn new() -> Self {
        Self(Vec::new())
    }
}

impl Comp {
    pub fn partial_eval(self, sig: &Sig, gen: &mut Gen, name: CaseName) -> Vec<(CaseName,Self)> {
        let cases = self.partial_eval_loop(sig, gen, Stack::new(), Vec::new(), name);
        // println!("partial_eval passing up {} cases", cases.len());
        cases
    }

    /// Only use this on comps that don't have contain case-splitting
    /// constructs (if-then-else and match).
    pub fn partial_eval_single_case(self, sig: &Sig, gen: &mut Gen) -> Self {
        // Give the partial_eval_loop the root() case name, which we
        // will discard.
        let mut cases = self.partial_eval_loop(
            sig,
            gen,
            Stack::new(),
            Vec::new(),
            CaseName::root()
        );
        assert!(
            cases.len() == 1,
            "partial_eval_single_case should only be called on comps that produce 1 case, got {} cases instead",
            cases.len(),
        );

        cases.pop().unwrap().1
        
    }

    fn partial_eval_loop(
        mut self,
        sig: &Sig,
        gen: &mut Gen,
        mut stack: Stack,
        mut anti_stack: Vec<Rebuild>,
        case_name: CaseName,
    ) -> Vec<(CaseName,Self)> {
        loop {
            match self {
                Self::Apply(m, vs) => {
                    stack.0.push(Frame::Args(vs));
                    self = *m;
                }
                Self::BindN(b, ps, m) => match b {
                    BinderN::Call(s,vs) => {
                        anti_stack.push(Rebuild::Call(s,vs,ps));
                        self = *m;
                    }
                    BinderN::Seq(m1) => {
                        stack.0.push(Frame::Seq(ps, *m));
                        self = *m1;
                    }
                }
                Self::Bind1(b, x, m) => match b {
                    Binder1::Eq(pos, vs1, vs2) => {
                        // We must flatten any tuple values among the two
                        // argument-sequences.
                        let mut vs1_flat = Vec::new();
                        for v in vs1 {
                            vs1_flat.append(&mut v.flatten());
                        }
                        let mut vs2_flat = Vec::new();
                        for v in vs2 {
                            vs2_flat.append(&mut v.flatten());
                        }
                        anti_stack.push(
                            Rebuild::Eq(pos, vs1_flat, vs2_flat, x)
                        );
                        self = *m;
                    }
                    Binder1::LogQuantifier(q, xs, body) => {
                        let mut body = *body;
                        // At this stage, we flatten the quantifier
                        // signature.
                        //
                        // Each quantified tuple becomes a vector of
                        // quantified atoms, and the existing identifier
                        // for the tuple is substituted by a tuple-value
                        // of those new identifiers for atoms.
                        let mut sig2 = Vec::new();
                        for (x,t) in xs {
                            match t.unwrap_atom() {
                                Ok(s) => sig2.push((x,VType::Atom(s))),
                                Err(t) => {
                                    let (mut ss,v) = gen.flatten_sig(t);
                                    sig2.append(&mut ss);
                                    body = body.substitute(&x, &v);
                                }
                            }
                        }
    
                        // The body should be evaluated with a fresh
                        // stack, so that its final Return does not pull
                        // pre-existing elements from the stack (external
                        // to the quantifier body) into the quantifier's
                        // body.

                        // Problem here: how can we split cases when inside a quantifier?
                        let mut body_cases = body.partial_eval_loop(sig, gen, Stack(Vec::new()), Vec::new(), case_name.clone());
                        assert!(
                            body_cases.len() == 1,
                            "For now, quantifier body should only have one case, but it had {} cases",
                            body_cases.len(),
                        );
                        let body = body_cases.pop().unwrap().1;
                        anti_stack.push(
                            Rebuild::Quantifier(q, sig2, body, x)
                        );
                        self = *m;
                    }
                    Binder1::LogNot(v) => {
                        anti_stack.push(Rebuild::Not(v,x));
                        self = *m;
                    }
                    Binder1::LogOpN(op,vs) => {
                        anti_stack.push(Rebuild::LogOpN(op, vs, x));
                        self = *m;
                    }
                }
                Self::Force(v) => match v {
                    Val::Thunk(m) => {
                        self = *m;
                    }

                    // If there is an unsubstituted var here, it must
                    // represent a primitive operator that we will
                    // intercept.
                    Val::Var(VName::Manual(s)) => {
                        match stack.0.pop() {
                            // Primitive operators should only appear as
                            // functions being applied to something, so we
                            // expect an Args frame on the stack.
                            //
                            // The input args remain unflattened here
                            // (this is dealt with later by
                            // expand_funs). The output, however, does get
                            // flattened.
                            Some(Frame::Args(vs)) => {
                                match sig.ops_map().get(&s) {
                                    Some(Op::Const(..)) => panic!(
                                        "Found constant {} in Force position",
                                        s,
                                    ),
                                    Some(Op::Direct(f)) => {
                                        self = Builder::lift(f.clone().rename(gen))
                                            .apply_rt(vs)
                                            .build(gen);
                                    }
                                    Some(Op::Symbol(..)) => {
                                        let x_result = gen.next();
                                        let mut flat_vs = Vec::new();
                                        for v in vs {
                                            flat_vs.append(&mut v.flatten());
                                        }
                                        anti_stack.push(Rebuild::LogOpN(
                                            LogOpN::Pred(SName(s),true),
                                            flat_vs,
                                            x_result.clone(),
                                        ));
                                        self = Comp::return1(x_result);
                                    }
                                    Some(Op::Pred(..)) => {
                                        let x_result = gen.next();
                                        anti_stack.push(Rebuild::LogOpN(
                                            LogOpN::Pred(SName(s),true),
                                            vs,
                                            x_result.clone(),
                                        ));
                                        self = Comp::return1(x_result);
                                    }
                                    Some(Op::Rec(op)) => {
                                        // This is exactly the same as the
                                        // Fun case below.
    
                                        // First, we need to flatten the
                                        // output type.
                                        let ts = op.output.clone().flatten();
                                        // We generate an ident for each
                                        // atomic type.
                                        let xs = gen.next_many(ts.len());
                                        // Then make a pattern to bind each ident.
                                        let ps = xs.clone().into_iter().map(Pattern::Atom).collect();
                                        // And a return value that gathers
                                        // all of the bound idents into a
                                        // tuple (with type matching the
                                        // original output type).
                                        let ret_v = Val::tuple(xs.into_iter().map(|x| x.val()).collect());
                                        anti_stack.push(Rebuild::Call(SName(s), vs, ps));
                                        self = Comp::return1(ret_v);
                                    }
                                    Some(Op::Fun(op)) => {
                                        // First, we need to flatten the
                                        // output type.
                                        let ts = op.output.clone().flatten();
                                        // We generate an ident for each
                                        // atomic type.
                                        let xs = gen.next_many(ts.len());
                                        // Then make a pattern to bind each ident.
                                        let ps = xs.clone().into_iter().map(Pattern::Atom).collect();
                                        // And a return value that gathers
                                        // all of the bound idents into a
                                        // tuple (with type matching the
                                        // original output type).
                                        let ret_v = Val::tuple(xs.into_iter().map(|x| x.val()).collect());
                                        anti_stack.push(Rebuild::Call(SName(s), vs, ps));
                                        self = Comp::return1(ret_v);
                                    }
                                    None => panic!(
                                        "Undeclared operator: {}",
                                        s,
                                    ),
                                }
                            }
                            Some(f) => {
                                panic!("pe reached Force({:?}) with {:?} on stack, rather than an Args.", s, f)
                            }
                            None => {
                                panic!("pe reached Force({:?}) with empty stack, rather than an Args.", s)
                            }
                        }
                    }
                    v => panic!("pe stuck on Force({:?})", v),
                }
                Self::Fun(xs, m) => match stack.0.pop() {
                    Some(Frame::Args(vs)) => {
                        self = *m;
                        assert!(xs.len() == vs.len(), "Arg count mismatch");
                        let names = xs.iter().map(|(x,_)| x);
                        for (x,v) in names.zip(&vs) {
                            self = self.substitute(x,v);
                        }
                    }
                    Some(f) => panic!("Eval Fun with stack top: {:?}", f),
                    None => {
                        self = Self::Fun(xs, m);
                        return vec![(
                            case_name,
                            self.rebuild_from_stack(anti_stack)
                        )];
                    },
                }
                Self::Ite(cond, then_b, else_b) => {
                    match cond {
                        Val::Literal(Literal::LogTrue) => { self = *then_b; }
                        Val::Literal(Literal::LogFalse) => { self = *else_b; }
                        Val::Var(x) => {
                            // Branches evaluate in parallel and don't
                            // affect each other, so we send two distinct
                            // copies of the stack down each.
                            //
                            // Note that they both get the same gen, so
                            // that vars are still unique across both
                            // branches.
                            let mut then_cases = then_b
                                .partial_eval_loop(sig, gen, stack.clone(), Vec::new(), case_name.clone());
                            assert!(
                                then_cases.len() == 1,
                                "For now, then-branch should have 1 case, but it had {} cases",
                                then_cases.len(),
                            );
                            let then_b = then_cases.pop().unwrap().1;

                            let mut else_cases = else_b
                                .partial_eval_loop(sig, gen, stack.clone(), Vec::new(), case_name.clone());
                            assert!(
                                else_cases.len() == 1,
                                "For now, else-branch should have 1 case, but it had {} cases",
                                else_cases.len(),
                            );
                            let else_b = else_cases.pop().unwrap().1;

                            self = Self::ite(x.val(), then_b, else_b);
                            return vec![(case_name, self.rebuild_from_stack(anti_stack))]
                        }
                        v => {
                            panic!("partial_eval found {:?} as ite-condition", v)
                        }
                    }
                }
                Self::Return(vs) => match stack.0.pop() {
                    Some(Frame::Seq(ps,m)) => {
                        assert!(
                            vs.len() == ps.len(),
                            "Got Frame::Seq with {} patterns for Return with {} vals (numbers should match)",
                            ps.len(),
                            vs.len(),
                        );
                        let mut ss = Vec::new();
                        for (p,v) in ps.into_iter().zip(vs) {
                            ss.append(&mut p.subs(v));
                        }
                        self = m.substitute_many(&ss);
                    }
                    Some(Frame::Args(v)) => {
                        panic!(
                            "pe stuck on return with {:?} on stack",
                            Frame::Args(v),
                        )
                    }
                    None => {
                        self = Self::Return(vs);
                        // println!("Exiting pe_loop for case {} via Return", case_name);
                        return vec![(
                            case_name,
                            self.rebuild_from_stack(anti_stack)
                        )];
                    }
                }
            }
        }
    }
}

impl Pattern {
    fn subs(self, v: Val) -> Vec<(VName, Val)> {
        match self {
            Self::NoBind => Vec::new(),
            Self::Atom(x) => vec![(x,v)],
            Self::Tuple(ps) => match v {
                Val::Tuple(vs) => {
                    assert!(
                        ps.len() == vs.len(),
                        "{}-tuple pattern matched against {}-tuple value, should match in size",
                        ps.len(),
                        vs.len(),
                    );
                    let mut ss = Vec::new();
                    for (p,v) in ps.into_iter().zip(vs) {
                        ss.append(&mut p.subs(v));
                    }
                    ss
                }
                v => {
                    panic!(
                        "{}-tuple pattern {:?} matched against non-tuple value {:?}",
                        ps.len(),
                        ps,
                        v,
                    )
                }
            }
        }
    }
}

impl Gen {
    fn flatten_sig(&mut self, t: VType) -> (Vec<(VName,VType)>, Val) {
        match t {
            VType::Atom(s) => {
                let x = self.next();
                (vec![(x.clone(), VType::Atom(s))], x.val())
            }
            VType::Tuple(ts) => {
                let mut ss = Vec::new();
                let mut vs = Vec::new();
                for t in ts {
                    let (mut ss_t, v_t) = self.flatten_sig(t);
                    ss.append(&mut ss_t);
                    vs.push(v_t);
                }
                (ss, Val::Tuple(vs))
            }
            vt => panic!("Can't flatten_sig {:?}", vt),
        }
    }
}

impl Val {
    pub fn flatten(self) -> Vec<Self> {
        match self.unwrap_non_tuple() {
            Ok(v) => vec![v],
            Err(vs) => {
                let mut out = Vec::new();
                for v in vs {
                    out.append(&mut v.flatten());
                }
                out
            }
        }
    }
    pub fn unwrap_non_tuple(self) -> Result<Self,Vec<Self>> {
        match self {
            Self::Tuple(vs) => Err(vs),
            v => Ok(v),
        }
    }
}
