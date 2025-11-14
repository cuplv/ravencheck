use crate::{
    Builder,
    Binder1,
    Comp,
    IGen,
    LogOpN,
    MatchArm,
    Oc,
    OpMode,
    Quantifier,
    Sig,
    Val,
};

impl Binder1 {
    pub fn eliminate_match(self, sig: &Sig, igen: &mut IGen) -> Self {
        match self {
            Self::LogQuantifier(q, xs, m) => Self::LogQuantifier(
                q, xs, Box::new(m.eliminate_match(sig,igen))
            ),
            b => b,
        }
    }
}

impl Comp {
    pub fn eliminate_match(self, sig: &Sig, igen: &mut IGen) -> Self {
        match self {
            Self::Bind1(b, x, m) => Self::Bind1(
                b.eliminate_match(sig,igen),
                x,
                Box::new(m.eliminate_match(sig,igen)),
            ),
            Self::BindN(b, ps, m) => Self::BindN(
                // BinderN::Call can appear here, but does not contain
                // computations that we need to eliminate on.
                b,
                ps,
                Box::new(m.eliminate_match(sig,igen)),
            ),
            Self::Ite(cond, then_b, else_b) => Self::Ite(
                cond,
                Box::new(then_b.eliminate_match(sig, igen)),
                Box::new(else_b.eliminate_match(sig, igen)),
            ),
            Self::Match(target, arms) => {
                match target {
                    Val::OpCode(OpMode::ZeroArgAsConst(_), code) => {
                        let (_,branch) = MatchArm::select(&code.ident, arms)
                            .expect("typed match should have matching arm");
                        branch
                    }
                    Val::Var(x, types, path, true) => {
                        let mut branches = Vec::<Comp>::new();
                        for (arm, branch) in arms.into_iter() {
                            // First, eliminate_matches within the
                            // branch.
                            let branch = branch.eliminate_match(sig,igen);

                            // Each branch should start with a
                            // quantification of any values in the
                            // constructor --- or an equation (to
                            // target) if the constructor has no
                            // values.
                            let branch = build_symbolic_branch(
                                Val::Var(
                                    x.clone(),
                                    types.clone(),
                                    path.clone(),
                                    true,
                                ),
                                arm,
                                branch,
                                sig,
                                igen,
                            );
                            branches.push(branch);
                        }
                        build_symbolic_match(branches, sig, igen)
                    }
                    Val::Var(_x, _types, _path, false) => {
                        panic!("Tried to match on a negative var, which should be bool type. You cannot match on bools, only enum types.")
                    }
                    target => todo!("match with target {:?}", target),
                }
            }
            Self::Return(vs) => Self::Return(vs),
            m => todo!("eliminate_match for {:?}", m),
        }
    }
}


fn build_symbolic_branch(
    target: Val,
    arm: MatchArm,
    branch: Comp,
    sig: &Sig,
    igen: &mut IGen,
) -> Comp {
    let types = match sig.get_applied_op_or_con(&arm.code) {
        Ok(Oc::Con(ts)) => ts,
        _ => panic!("match arm code was not for a constructor: {:?}", &arm.code),
    };
    let xs = arm.binders.into_iter().map(|p| p.unwrap_vname().unwrap());
    let mut rel_args: Vec<Val> =
        xs.clone().into_iter().map(|x| x.val()).collect();
    rel_args.push(target.clone());
    let qsig = xs.zip(types).collect::<Vec<_>>();

    let cond = if qsig.len() == 0 {
        // Equate target to the constructor as a constant.
        Builder::return_(target)
            .eq_ne(
                true,
                Builder::return_(arm.code.as_zero_arg_as_const())
            )
    } else {
        // Relate target to the newly quantified vars, using the
        // relational abstraction of the arm's opcode.
        Builder::force(Val::OpCode(OpMode::RelAbs, arm.code))
            .apply_v(rel_args)
    };
    // The condition should then imply the remaining comp.
    let branch =
        Builder::log_op(LogOpN::Or, [cond.not(), Builder::lift(branch)])
        .into_quantifier(Quantifier::Forall, qsig);
    let b = branch.build_with(igen);
    // println!("\nBuilt match branch: {:?}\n", b);
    b
}

fn build_symbolic_match(
    mut branches: Vec<Comp>,
    sig: &Sig,
    igen: &mut IGen,
) -> Comp {
    if branches.len() == 1 {
        let b = branches.pop().unwrap().partial_eval_single_case(sig, igen);
        // println!("\nBuilt (single) matcher: {:?}\n", b);
        b
    } else {
        let branches: Vec<Builder> =
            branches.into_iter().map(Builder::lift).collect();
        let b = Builder::log_op(LogOpN::And, branches)
            .build_with(igen)
            .partial_eval_single_case(sig, igen);
        // println!("\nBuilt matcher: {:?}\n", b);
        b
    }
}
