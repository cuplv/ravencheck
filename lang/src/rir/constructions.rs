use crate::{
    BType,
    Builder,
    OpCode,
    Val,
    VType,
    substruct_code,
};

/// If there are zero args, gives `ZeroArgAsConst(code) == output`.
///
/// If there are non-zero args, gives `RelAbs(code)(inputs, output)`.
pub fn applied_code_clause(
    code: OpCode,
    inputs: Vec<Val>,
    output: Val,
) -> Builder {
    if inputs.len() == 0 {
        Val::zero_arg_as_const(code).ret().builder()
            .is_eq(output.ret())
    } else {
        let mut args = inputs;
        args.push(output);
        Val::rel_abs(code).force().builder()
            .apply_v(args)
    }
}

pub fn totality_axiom(
    code: OpCode,
    inputs: Vec<VType>,
    output: VType,
) -> Builder {
    Builder::forall_many(inputs, |inputs| {
        Builder::exists(output, |output| {
            let mut args = inputs;
            args.push(output);
            let f = Val::rel_abs(code).force();
            f.builder().apply_v(args)
        })
    })
}

/// RelAbs(code)(inputs) == output1 and RelAbs(code)(inputs) ==
/// output2 implies that output1 == output2.
pub fn fun_axiom(
    code: OpCode,
    inputs: Vec<VType>,
    output: VType,
) -> Builder {
    Builder::forall_many(inputs, |inputs| {
        Builder::forall(output.clone(), |output1| {
            Builder::forall(output, |output2| {
                let mut args1 = inputs.clone();
                args1.push(output1.clone());
                let mut args2 = inputs;
                args2.push(output2.clone());
                let f = Val::rel_abs(code).force();
                let f1 = f.clone().builder().apply_v(args1);
                let f2 = f.builder().apply_v(args2);
                f1.and(f2).implies(
                    output1.ret().builder()
                        .is_eq(output2.ret()))
            })
        })
    })
}

impl Builder {

    pub fn is_substruct(
        t: BType,
        b1: Builder,
        b2: Builder,
    ) -> Builder {
        let code = substruct_code(t);
        Val::op(code.clone()).force().builder().apply([b1, b2])
    }
    
    pub fn is_substruct_v(
        t: BType,
        v1: Val,
        v2: Val,
    ) -> Builder {
        let code = substruct_code(t);
        Val::op(code.clone()).force().builder().apply_v([v1, v2])
    }

    pub fn substruct_axioms(
        t: BType,
        cons: Vec<(OpCode, Vec<VType>)>,
    ) -> Vec<Builder> {
        let code = substruct_code(t.clone());
        let f = Val::op(code).force();

        let mut ts = std::iter::repeat(VType::Base(t.clone()));
        let mut take_ts = |n: usize| {
            (&mut ts).take(n).collect::<Vec<_>>()
        };

        let _ = take_ts(5);

        let f_clone = f.clone();
        let reflexive = Builder::forall_many(take_ts(1), move |vs| {
            let [v] = vs.try_into().unwrap();
            let subs = |a: Val, b: Val| {
                f_clone.clone().builder().apply_v([a, b])
            };
            subs(v.clone(), v)
        });

        let f_clone = f.clone();
        let transitive =
            Builder::forall_many(take_ts(3), move |vs| {
                let [v1, v2, v3] = vs.try_into().unwrap();
                // let f = Val::op(code.clone()).force();
                let subs = |a: Val, b: Val| {
                    f_clone.clone().builder().apply_v([a, b])
                };
                subs(v1.clone(), v2.clone())
                    .and(subs(v2, v3.clone()))
                    .implies(subs(v1, v3))
            });

        let f_clone = f.clone();
        let anti_symmetric =
            Builder::forall_many(take_ts(2), move |vs| {
                let [v1, v2] = vs.try_into().unwrap();
                // let f = Val::op(code.clone()).force();
                let subs = |a: Val, b: Val| {
                    f_clone.clone().builder().apply_v([a, b])
                };
                subs(v1.clone(), v2.clone())
                    .and(subs(v2.clone(), v1.clone()))
                    .implies(Builder::is_eq_v(v1,v2))
            });

        let mut out = Vec::new();

        // Add the partial-order axioms
        out.push(reflexive);
        out.push(transitive);
        out.push(anti_symmetric);

        // Add an axiom for each constructor
        for (con_code, input_ts) in cons {
            // Find each self-type (recursive component) among the
            // inputs.  Each of those inputs is substruct (not-equal)
            // related to the output.
            let output_t = VType::Base(t.clone());
            let f_clone = f.clone();
            out.push(Builder::forall_many(input_ts.clone(), move |input_xs| {
                Builder::forall(output_t.clone(), move |output_x| {
                    let mut srels: Vec<Builder> = Vec::new();
                    for (ix,it) in input_xs.iter().zip(input_ts) {
                        if it == output_t {
                            srels.push(
                                f_clone.clone().builder()
                                    .apply_v([ix.clone(), output_x.clone()])
                                    .and(Builder::is_ne_v(
                                        ix.clone(),
                                        output_x.clone()
                                    ))
                            );
                        }
                    }
                    if srels.len() > 0 {
                        applied_code_clause(con_code, input_xs, output_x)
                            .implies(Builder::and_many(srels))
                    } else {
                        Builder::true_()
                    }
                })
            }));
        }
        // todo!("add substructure axioms for contstructors");

        out
    }

}
    

/// If two calls to the same constructor give the same value, then the
/// two sets of inputs must be identical.
pub fn same_con_exclusion_axiom(
    code: OpCode,
    inputs: Vec<VType>,
    output: VType,
) -> Builder {
    Builder::forall_many(inputs.clone(), |inputs1| {
        Builder::forall_many(inputs, |inputs2| {
            Builder::forall(output, |output| {
                let f1 = applied_code_clause(
                    code.clone(),
                    inputs1.clone(),
                    output.clone(),
                );
                let f2 = applied_code_clause(
                    code,
                    inputs2.clone(),
                    output,
                );                
                let eq_clauses = inputs1
                    .into_iter()
                    .zip(inputs2)
                    .map(|(i1,i2)| i1.ret().builder().is_eq(i2.ret()))
                    .collect::<Vec<_>>();
                f1.and(f2).implies(Builder::and_many(eq_clauses))
            })
        })
    })
}

/// Two calls to two different constructors never give the same
/// output.
pub fn diff_con_exclusion_axiom(
    code1: OpCode,
    inputs1: Vec<VType>,
    code2: OpCode,
    inputs2: Vec<VType>,
    output: VType,
) -> Builder {
    Builder::forall_many(inputs1, |inputs1| {
        Builder::forall_many(inputs2, |inputs2| {
            Builder::forall(output, |output| {

                let f1 = applied_code_clause(
                    code1,
                    inputs1,
                    output.clone()
                );

                let f2 = applied_code_clause(
                    code2,
                    inputs2,
                    output,
                );

                f1.and(f2).not()
            })
        })
    })
}
