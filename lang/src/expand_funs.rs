use crate::{
    Binder1,
    BinderN,
    Builder,
    Comp,
    Gen,
    LogOpN,
    Op,
    Quantifier,
    Rebuild,
    Sig,
    Val,
    VName,
    FunOp,
    PredOp,
};

fn expand_fun(op: FunOp, vs: Vec<Val>, xs: Vec<VName>, m: Comp, sig: &Sig, gen: &mut Gen) -> Comp {
    assert!(
        !op.output.contains_prop(),
        "Can't have bool-output primitive function. Define a predicate instead."
    );
    let flat_output = op.output.flatten();
    assert!(
        xs.len() == flat_output.len(),
        "expand_fun mismatch between var-count and output-type-count",
    );
    let output_tuple = Val::tuple(
        xs.clone()
            .into_iter()
            .map(|x| x.val())
            .collect()
    );
    let q_sig = xs.into_iter().zip(flat_output).collect();

    let mut disjuncts: Vec<Builder> = op.axioms.into_iter().map(|axiom| {
        Builder::new(|gen| axiom.rename(gen))
            .flatten()
            .apply_v(vs.clone())
            .flatten()
            .apply_v(vec![output_tuple.clone()])
            .not()
    }).collect();
    disjuncts.push(Builder::lift(m));
    let new_body =
        Builder::log_op(LogOpN::Or, disjuncts).build(gen);

    let x_result = gen.next();
    let new_m =
        Comp::quant_many(
            Quantifier::Forall,
            q_sig,
            new_body.normal_form_single_case(sig,gen),
            x_result.clone(),
            Comp::return1(x_result),
        );
    new_m
}

fn expand_pred(op: PredOp, vs: Vec<Val>, x: VName, m: Comp, sig: &Sig, gen: &mut Gen, is_pos: bool) -> Comp {
    let sig_clone1 = sig.clone();
    let sig_clone2 = sig.clone();

    // Build the POSITIVE branch: one big disjunction. SOME axiom is
    // FALSE, OR the condition with 'true' plugged in is TRUE.
    //
    // !axiom_0 OR ... OR !axiom_n OR condition[true]
    let mut t_disjuncts: Vec<Builder> =
        op.axioms.clone().into_iter().map(|axiom| {
            Builder::new(|gen| axiom.rename(gen))
                .flatten()
                .apply_v(vs.clone())
                .not()
        })
        .collect();
    let t_val = Val::from_bool(is_pos);
    t_disjuncts.push(
        Builder::lift(m.clone().substitute(&x, &t_val))
    );
    let pos_branch = Builder::new(move |gen| {
        Builder::log_op(LogOpN::Or, t_disjuncts)
            .build(gen)
            .normal_form_single_case(&sig_clone1, gen)
    });

    // Build the FALSE branch: disjunction with a conjunction. ALL
    // axioms are TRUE, OR the condition with 'false' plugged in is
    // TRUE.
    //
    // (axiom_0 AND ... AND axiom_n) OR condition[false]
    //
    // Note that if there are no axioms, this collapses to simply:
    //
    // true
    //
    // We use if-then-else for this case below, because easy_smt
    // panics when you construct an AND_MANY node with no arguments.
    let f_conjuncts: Vec<Builder> =
        op.axioms.clone().into_iter().map(|axiom| {
            Builder::new(|gen| axiom.rename(gen))
                .flatten()
                .apply_v(vs.clone())
        })
        .collect();
    let f_val = Val::from_bool(!is_pos);
    let neg_branch = if f_conjuncts.len() > 0 {
        Builder::new(move |gen| {
            Builder::log_op(LogOpN::Or, [
                Builder::log_op(LogOpN::And, f_conjuncts),
                Builder::lift(m.clone().substitute(&x, &f_val))
            ])
                .build(gen)
                .normal_form_single_case(&sig_clone2, gen)
            })
    } else {
        Builder::return_(Val::true_())
    };
    
    Builder::log_op(LogOpN::And, [
        pos_branch,
        neg_branch,
    ])
        .build(gen)
        .normal_form_single_case(sig,gen)
}

impl Comp {
    pub fn expand_funs(mut self, sig: &Sig, gen: &mut Gen, mut anti_stack: Vec<Rebuild>) -> Self {
        loop {
            match self {
                Self::Bind1(b, x, m) => {
                    match b {
                        Binder1::LogOpN(LogOpN::Pred(s,is_pos), vs) => {
                            match sig.ops_map().get(&s.0) {
                                Some(Op::Const(..)) => {
                                    panic!("Got constant op {:?} in Pred", s)
                                }
                                Some(Op::Direct(..)) => {
                                    panic!("Got direct fun {:?} in Pred", s)
                                }
                                Some(Op::Pred(op)) => {
                                    println!("Expanding pred {}...", &s.0);
                                    self = expand_pred(op.clone(), vs, x, *m, sig, gen, is_pos);
                                    break;
                                }
                                Some(Op::Fun(_op)) => {
                                    panic!("Got fun op {:?} in Pred", s)
                                }
                                Some(Op::Rec(..)) => todo!("expand_funs for RecOp"),
                                Some(Op::Symbol(_op)) => {
                                    anti_stack.push(Rebuild::LogOpN(
                                        LogOpN::Pred(s,is_pos),
                                        vs,
                                        x,
                                    ));
                                    self = *m;
                                }
                                // Treat None like a Symbol, since
                                // it's probably a relational
                                // abstraction.
                                None => {
                                    anti_stack.push(Rebuild::LogOpN(
                                        LogOpN::Pred(s,is_pos),
                                        vs,
                                        x,
                                    ));
                                    self = *m;
                                }
                                // None => {
                                //     panic!(
                                //         "Symbol {:?} not found in sig",
                                //         s,
                                //     )
                                // }
                            }
                        }
                        Binder1::LogQuantifier(q, xs, body) => {
                            let body = body.expand_funs(sig,gen,Vec::new());
                            anti_stack.push(Rebuild::Quantifier(q, xs, body, x));
                            self = *m;
                        },
                        b => {
                            anti_stack.push(Rebuild::Bind1(b, x));
                            self = *m;
                        }
                    }
                }
                Self::BindN(BinderN::Call(s, vs), ps, m) => {
                    let xs = ps
                        .into_iter()
                        .map(|p| p.unwrap_atom().expect("Call should only be bound to flat patterns"))
                        .collect();
                    match sig.ops_map().get(&s.0) {
                        Some(Op::Fun(op)) => {
                            println!("Expanding call {}...", &s.0);
                            self = expand_fun(op.clone(), vs, xs, *m, sig, gen);
                            break;
                        }
                        Some(Op::Pred(_op)) => {
                            panic!("Got pred op {:?} in Fun", s)
                        }
                        Some(Op::Rec(op)) => {
                            println!("Expanding call {}...", &s.0);
                            self = expand_fun(op.clone().as_fun_op(), vs, xs, *m, sig, gen);
                            break;
                        }
                        r => panic!("Can't expand_fun on {:?}", r),
                    }
                }
                Self::Ite(cond, then_b, else_b) => {
                    let then_b = then_b.expand_funs(sig,gen,Vec::new());
                    let else_b = else_b.expand_funs(sig,gen,Vec::new());
                    self = Self::ite(cond, then_b, else_b);
                    break;
                }
                Self::Return(vs) => {
                    self = Self::Return(vs);
                    break;
                }
                m => panic!("expand_funs: Unexpected Comp {:?}", m),
            }
        }
        self.rebuild_from_stack(anti_stack)
    }
}
