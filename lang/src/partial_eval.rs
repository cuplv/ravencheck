use crate::{
    Binder1,
    BinderN,
    Builder,
    CaseName,
    Comp,
    IGen,
    Literal,
    LogOpN,
    Oc,
    Op,
    OpCode,
    OpMode,
    Pattern,
    Rebuild,
    Sig,
    Val,
    Ident,
    VType,
};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Frame {
    Seq(Vec<Pattern>, Comp),
    Args(Vec<VType>,Vec<Val>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Stack(Vec<Frame>);

impl Stack {
    pub fn new() -> Self {
        Self(Vec::new())
    }
}

impl Comp {
    pub fn partial_eval(self, sig: &Sig, igen: &mut IGen, name: CaseName) -> Vec<(CaseName,Self)> {
        let cases = self.partial_eval_loop(sig, igen, Stack::new(), Vec::new(), name);
        // println!("partial_eval passing up {} cases", cases.len());
        // println!("\npartial_eval returning {:?}\n", cases);
        cases
    }

    /// Only use this on comps that don't have contain case-splitting
    /// constructs (if-then-else and match).
    pub fn partial_eval_single_case(self, sig: &Sig, igen: &mut IGen) -> Self {
        // Give the partial_eval_loop the root() case name, which we
        // will discard.
        let mut cases = self.partial_eval_loop(
            sig,
            igen,
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
        igen: &mut IGen,
        mut stack: Stack,
        mut anti_stack: Vec<Rebuild>,
        case_name: CaseName,
    ) -> Vec<(CaseName,Self)> {
        loop {
            match self {
                Self::Apply(m, targs, vs) => {
                    stack.0.push(Frame::Args(targs,vs));
                    self = *m;
                }
                Self::BindN(b, ps, m) => match b {
                    BinderN::Call(oc,vs) => {
                        anti_stack.push(Rebuild::Call(oc,vs,ps));
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
                            match t.unwrap_base() {
                                Ok(s) => sig2.push((x, VType::Base(s))),
                                Err(t) => {
                                    let (mut ss,v) = igen.flatten_sig(t);
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
                        let mut body_cases = body.partial_eval_loop(sig, igen, Stack(Vec::new()), Vec::new(), case_name.clone());
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
                    Val::Var(x, types, path, false) => panic!(
                        "Should not force a bool, but {:?} was negated, which should only happen if it's a bool",
                        Val::Var(x, types, path, false),
                    ),
                    Val::Var(Ident::Manual(s), types, path, true) => {
                        let oc = OpCode { ident: s.clone(), types, path };

                        match stack.0.pop() {
                            // Primitive operators should only be
                            // forced as as functions being applied to
                            // something, so we expect an Args frame
                            // on the stack.
                            //
                            // The input args remain unflattened here
                            // (this is dealt with later by
                            // expand_funs). The output, however, does get
                            // flattened.
                            Some(Frame::Args(_targs,vs)) => {
                                match sig.get_applied_op_or_con(&oc) {
                                    Ok(Oc::Con(_inputs)) => {
                                        // self = Comp::return1(Val::EnumCon(oc, vs));

                                        if vs.len() == 0 {
                                            // let ret_v = Val::OpCode(OpMode::ZeroArgAsConst, oc);
                                            let ret_v = oc.as_zero_arg_as_const();
                                            self = Comp::return1(ret_v);
                                        } else {
                                            // First, we need to flatten the
                                            // output type.
                                            let output = VType::Base(oc.get_enum_type().unwrap());
                                            let ts = output.flatten();
                                            // We generate an ident for each
                                            // atomic type.
                                            let xs = igen.next_many(ts.len());
                                            // Then make a pattern to bind each ident.
                                            let ps = xs.clone().into_iter().map(Pattern::Atom).collect();
                                            // And a return value that gathers
                                            // all of the bound idents into a
                                            // tuple (with type matching the
                                            // original output type).
                                            let ret_v = Val::tuple(xs.into_iter().map(|x| x.val()).collect());
                                            anti_stack.push(Rebuild::Call(oc, vs, ps));
                                            self = Comp::return1(ret_v);
                                        }
                                    }
                                    Ok(Oc::Op(Op::Const(..))) => panic!(
                                        "Found constant {} in Force position",
                                        oc,
                                    ),
                                    Ok(Oc::Op(Op::Direct(f))) => {
                                        self = Builder::lift(f.clone().rename(igen))
                                            .apply_rt(vs)
                                            .build_with(igen);
                                    }
                                    Ok(Oc::Op(Op::Symbol(..))) => {
                                        let x_result = igen.next();
                                        let mut flat_vs = Vec::new();
                                        for v in vs {
                                            flat_vs.append(&mut v.flatten());
                                        }
                                        anti_stack.push(Rebuild::LogOpN(
                                            LogOpN::Pred(oc,true),
                                            flat_vs,
                                            x_result.clone(),
                                        ));
                                        self = Comp::return1(x_result);
                                    }
                                    Ok(Oc::Op(Op::Pred(..))) => {
                                        let x_result = igen.next();
                                        anti_stack.push(Rebuild::LogOpN(
                                            LogOpN::Pred(oc,true),
                                            vs,
                                            x_result.clone(),
                                        ));
                                        self = Comp::return1(x_result);
                                    }
                                    Ok(Oc::Op(Op::Rec(op))) => {
                                        // This is exactly the same as the
                                        // Fun case below.
    
                                        // First, we need to flatten the
                                        // output type.
                                        let ts = op.output.clone().flatten();
                                        // We generate an ident for each
                                        // atomic type.
                                        let xs = igen.next_many(ts.len());
                                        // Then make a pattern to bind each ident.
                                        let ps = xs.clone().into_iter().map(Pattern::Atom).collect();
                                        // And a return value that gathers
                                        // all of the bound idents into a
                                        // tuple (with type matching the
                                        // original output type).
                                        let ret_v = Val::tuple(xs.into_iter().map(|x| x.val()).collect());
                                        anti_stack.push(Rebuild::Call(oc, vs, ps));
                                        self = Comp::return1(ret_v);
                                    }
                                    Ok(Oc::Op(Op::Fun(op))) => {
                                        if vs.len() == 0 {
                                            // let ret_v = Val::OpCode(OpMode::ZeroArgAsConst, oc);
                                            let ret_v = oc.as_zero_arg_as_const();
                                            self = Comp::return1(ret_v);
                                        } else {
                                            // First, we need to flatten the
                                            // output type.
                                            let ts = op.output.clone().flatten();
                                            // We generate an ident for each
                                            // atomic type.
                                            let xs = igen.next_many(ts.len());
                                            // Then make a pattern to bind each ident.
                                            let ps = xs.clone().into_iter().map(Pattern::Atom).collect();
                                            // And a return value that gathers
                                            // all of the bound idents into a
                                            // tuple (with type matching the
                                            // original output type).
                                            let ret_v = Val::tuple(xs.into_iter().map(|x| x.val()).collect());
                                            anti_stack.push(Rebuild::Call(oc, vs, ps));
                                            self = Comp::return1(ret_v);
                                        }
                                    }
                                    Err(e) => panic!("Invalid OpCode '{}': {}", oc, e),
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

                    // Only the RelAbs mode is legal here,
                    // representing the relation being applied to some
                    // arguments.
                    //
                    // Handled just like the Symbol case above.
                    Val::OpCode(OpMode::RelAbs, oc) => {
                        match stack.0.pop() {
                            Some(Frame::Args(_,vs)) => {
                                let x_result = igen.next();
                                let mut flat_vs = Vec::new();
                                for v in vs {
                                    flat_vs.append(&mut v.flatten());
                                }
                                anti_stack.push(Rebuild::LogOpN(
                                    LogOpN::Pred(oc,true),
                                    flat_vs,
                                    x_result.clone(),
                                ));
                                self = Comp::return1(x_result);
                            }
                            Some(f) => {
                                panic!("pe reached Force(RelAbs({:?})) with {:?} on stack, rather than an Args.", oc, f)
                            }
                            None => {
                                panic!("pe reached Force(RelAbs({:?})) with empty stack, rather than an Args.", oc)
                            }
                        }
                    }

                    v => panic!("pe stuck on Force({:?})", v),
                }
                Self::Fun(xs, m) => match stack.0.pop() {
                    Some(Frame::Args(targs,vs)) => {
                        self = *m;
                        assert!(targs.len() == 0, "Type args given to regular function");
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
                        Val::Var(x, types, path, is_pos) => {
                            // Branches evaluate in parallel and don't
                            // affect each other, so we send two distinct
                            // copies of the stack down each.
                            //
                            // Note that they both get the same gen, so
                            // that vars are still unique across both
                            // branches.
                            let mut then_cases = then_b
                                .partial_eval_loop(sig, igen, stack.clone(), Vec::new(), case_name.clone());
                            assert!(
                                then_cases.len() == 1,
                                "For now, then-branch should have 1 case, but it had {} cases",
                                then_cases.len(),
                            );
                            let then_b = then_cases.pop().unwrap().1;

                            let mut else_cases = else_b
                                .partial_eval_loop(sig, igen, stack.clone(), Vec::new(), case_name.clone());
                            assert!(
                                else_cases.len() == 1,
                                "For now, else-branch should have 1 case, but it had {} cases",
                                else_cases.len(),
                            );
                            let else_b = else_cases.pop().unwrap().1;

                            self = Self::ite(Val::Var(x, types, path, is_pos), then_b, else_b);
                            return vec![(case_name, self.rebuild_from_stack(anti_stack))]
                        }
                        v => {
                            panic!("partial_eval found {:?} as ite-condition", v)
                        }
                    }
                }
                Self::Match(target, arms) => {
                    match target {
                        // Val::OpCode(OpMode::ZeroArgAsConst, code) => {
                        //     todo!("Got the OpCode ZeroArgAsConst match target: {}", code);
                        //     let (_,branch) = MatchArm::select(&code.ident, arms)
                        //         .expect("typed match should have matching arm");
                        //     self = branch;
                        // }
                        Val::Var(x, types, path, true) => {
                            // As with Ite, match cases evaluate in
                            // parallel and don't affect each other,
                            // so we send distinct copies of the stack
                            // down each.
                            let arms = arms
                                .into_iter()
                                .map(|(arm, branch)| {
                                    // Before evaluating the branch,
                                    // we need to handle the bound
                                    // contents of the constructor
                                    // just like we would from a
                                    // quantifier.

                                    // First, get the list of inputs
                                    // types for the arm's
                                    // constructor.

                                    // Next, zip them with the arm's
                                    // patterns (unwrapped into
                                    // vnames).

                                    // But we can't "modify the match
                                    // signature" like we do for
                                    // quantifiers... how do we save
                                    // the fact that tuples have been
                                    // split?

                                    // I'll leave this for later, and
                                    // avoid putting tuples in enums
                                    // for now.

                                    let mut branch_cases = branch
                                        .partial_eval_loop(
                                            sig,
                                            igen,
                                            stack.clone(),
                                            Vec::new(),
                                            case_name.clone(),
                                        );
                                    let branch =
                                        branch_cases.pop().unwrap().1;
                                    (arm, Box::new(branch))
                                })
                                .collect();

                            self = Self::Match(
                                Val::Var(x, types, path, true),
                                arms,
                            );
                            return vec![(case_name, self.rebuild_from_stack(anti_stack))]
                        }
                        Val::Var(_x, _types, _path, false) => {
                            panic!("Tried to match on a negative var, which should be bool type. You cannot match on bools, only enum types.")
                        }
                        target => todo!("match with target {:?}", target),
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
                    Some(Frame::Args(targs,v)) => {
                        panic!(
                            "pe stuck on return with {:?} on stack",
                            Frame::Args(targs,v),
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
                // c => todo!("partial_eval loop {:?}", c),
            }
        }
    }
}

impl Pattern {
    fn subs(self, v: Val) -> Vec<(Ident, Val)> {
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

impl IGen {
    fn flatten_sig(&mut self, t: VType) -> (Vec<(Ident,VType)>, Val) {
        match t {
            VType::Base(s) => {
                let x = self.next();
                (vec![(x.clone(), VType::Base(s))], x.val())
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
