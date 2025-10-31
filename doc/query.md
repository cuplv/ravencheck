# Original query

```
fn add_twice(a: Nat, b: Nat) -> Nat {
    if b == Nat::Z {
        a
    } else {
        add(add(a, b), b)
    }
}

#[verify]
fn add_twice_monotonic() -> bool {
    !exists(|x: Nat, y: Nat| {
        gt(x, add_twice(x,y))
    })
}
```

# 1. Convert to CBPV

Ravencheck's internal representation
is Call-By-Push-Value style.
The conversion from surface-level Rust sytnax
is implemented in `lang/src/syn_to_cbpv.rs`.

The converted query example here
is written out using Rust syntax,
but internally Ravencheck uses the AST 
defined in `lang/src/cbpv.rs`
to represented the code.
The AST is defined by the mutually-inductive
`Comp` and `Val` enum types.

```
fn add_twice(a: Nat, b: Nat) -> Nat {
    let v0 = b == Nat::Z;
    if v0 {
        return a
    } else {
        let v1 = add(a, b);
        let v2 = add(v1, b);
        return v2
    }
}

#[verify]
fn add_twice_monotonic() -> bool {
    let v3 = exists(|x: Nat, y: Nat| {
        let v4 = add_twice(x,y);
        let v5 = gt(x, v4);
        return v5
    });
    let v6 = !v3;
    return v6
}
```

# 2. Partial evaluaion

In this step, queries are evaluated as much as possible,
leaving only symbolic values and functions.
In this example, the `add_twice` function 
is eliminated by inlining.
In contrast, calls 
to the primitive/uninterpreted `add` function 
remain.

This is performed 
by functions in `lang/src/partial_eval.rs`.

The result is still represented
using the `Comp`/`Val` AST.

```
#[verify]
fn add_twice_monotonic() -> bool {
    let v3 = exists(|x: Nat, y: Nat| {
        let v0 = y == Nat::Z;
        if v0 {
            let v5 = gt(x, x);
            return v5
        } else {
            let v1 = add(x, y);
            let v2 = add(v1, y);
            let v5 = gt(x, v2);
            return v2
        }
    });
    let v6 = !v3;
    return v6
}
```

# 3. Negation-normal-form

Performed by `lang/src/neg_normal_form.rs`.

```
#[verify]
fn add_twice_monotonic() -> bool {
    forall(|x: Nat, y: Nat| {
        let v0 = y == Nat::Z;
        if v0 {
            let v5 = !gt(x, x);
            return v5
        } else {
            let v1 = add(x, y);
            let v2 = add(v1, y);
            let v5 = !gt(x, v2);
            return v5
        }
    });
}
```

# 4. Relational abstraction

Performed by `lang/src/expand_funs.rs`.

```
#[verify]
fn add_twice_monotonic() -> bool {
    forall(|x: Nat, y: Nat| {
        let v0 = y == Nat::Z;
        if v0 {
            let v5 = !gt(x, x);
            return v5
        } else {
            forall(|v1: Nat| implies(
                add_ra(x, y, v1),
                forall(|v2: Nat| implies(
                    add_ra(v1, y, v2),
                    {
                        let v5 = !gt(x, v2);
                        return v5
                    }
                ))
            ))
        }
    })
}
```

# 5. Conversion to SMT

Performed by `lang/src/smt/internal.rs`.

This takes the `Comp`/`Val` AST
and produces an `easy-smt` AST,
which is then converted by the `easy-smt` package
into actual SMTLIB code and fed to CVC5.
