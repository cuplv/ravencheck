use crate::{
    Builder,
    OpCode,
    Val,
    VType,
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
