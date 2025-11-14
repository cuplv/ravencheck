use crate::{
    Binder1,
    BinderN,
    Comp,
    IGen,
    Ident,
    LogOpN,
    MatchArm,
    Pattern,
    Quantifier,
    VType,
    Val,
};

/**
Use `Builder` to easily define and compose Raven IR terms.

Raven IR terms are represented
by the [`Comp`] and [`Val`] enum types.
These types are good for processing,
but using them to manually construct IR terms is inconvenient,
and so we use `Builder` for this task.
For example, suppose we wanted to construct
the Raven IR equivalent of
the Rust expression `(x || y) && true`.
Using `Builder`, we can write:

```
use ravenlang::{Builder, Comp};

let e: Comp =
    Builder::var("x")
    .or(Builder::var("y"))
    .and(Builder::true_())
    .build_no_context();

println!("The expression: {:?}", e)
```

The `.build_no_context()` line "compiles" the builder,
producing a `Comp` that is equivalent
to the following direct definition.

```
use ravenlang::{Binder1, Comp, Ident, LogOpN, Val};

let e: Comp =
    Comp::Bind1(
        Binder1::LogOpN(
            LogOpN::Or,
            vec![
                Val::var(Ident::new("x")),
                Val::var(Ident::new("y"))
            ]
        ), 
        Ident::new("i0"),
        Box::new(Comp::Bind1(
            Binder1::LogOpN(
                LogOpN::And,
                vec![
                    Val::var(Ident::Auto(0)),
                    Val::true_(),
                ]
            ),
            Ident::new("i1"),
            Box::new(Comp::Return(
                vec![Val::var(Ident::Auto(1))]
            ))
        ))
    );

println!("The expression: {:?}", e)
```

Notice that, in the direct definition,
we had to invent two new names
for intermediate variables: `i0` and `i1`.
The `Builder` handles this creation of fresh names for us,
filling them in when we call [`Builder::build_no_context`].
*/
pub struct Builder {
    fun: Box<dyn FnOnce(&mut IGen) -> Comp>,
}

impl Comp {
    pub fn builder(self) -> Builder {
        Builder{
            fun: Box::new(|_igen: &mut IGen| self)
        }
    }
}

impl From<Comp> for Builder {
    fn from(comp: Comp) -> Self {
        comp.builder()
    }
}

impl Builder {

    /// Build a `Comp`, using a new [`IGen`] to fill in fresh variable
    /// names.
    ///
    /// Do not use this to build a `Comp` that will be nested within
    /// another `Comp`, since the new `IGen` does not know about
    /// existing in-scope variable names and might shadow them. In
    /// that case, use [`Builder::build_with`] instead, and pass in
    /// the `IGen` that was used to create the other in-scope variable
    /// names.
    pub fn build_no_context(self) -> Comp {
        self.build_with(&mut IGen::new())
    }

    /** 
    Build a `Comp`,
    using the provided [`IGen`] reference
    to generate fresh variable names.
    The `IGen` will be advanced
    so that using it in the future
    does not shadow the generated names.
    */
    pub fn build_with(self, igen: &mut IGen) -> Comp {
        (self.fun)(igen)
    }

    /**
    Get a fresh `Ident`
    and use it to modify an existing `Builder`.

    In the following example, `b2` is equivalent
    to `|x: bool| (true, x)`,
    but uses an auto-generated name in place of `x`.

    ```
    use ravenlang::{Builder, VType};

    let b = Builder::true_();

    let b2 = b.igen(|b||x| {
        Builder::tuple([b, Builder::var(x.clone())])
            .into_fun([(x, VType::prop())])
    });
    ```
    */
    pub fn igen<F1,F2>(self, f: F1) -> Self
    where
        F1: FnOnce(Self) -> F2 + 'static,
        F2: FnOnce(Ident) -> Self,
    {
        Self::new(|igen| {
            let m = self.build_with(igen);
            let x = igen.next();
            f(Builder::lift(m))(x).build_with(igen)
        })
    }

    /**
    Create a new ident and use it in a builder.

    The following example creates a Raven IR function equivalent to
    `|i0: bool| { (i0,i0) }`, but with a unique generated `Ident`
    in place of `i0`.
    ```
    use ravenlang::{Builder, VType};

    let b = Builder::with_x(|i0| {
        let body = Builder::tuple([
            Builder::var(i0.clone()),
            Builder::var(i0.clone()),
        ]);

        body.into_fun([(i0, VType::prop())])
    });
    ```
    */
    pub fn with_x<F>(f: F) -> Self
    where F: FnOnce(Ident) -> Self + 'static,
    {
        Self::new(move |igen| {
            let x = igen.next();
            f(x).build_with(igen)
        })
    }

    /**
    This works just like [`Builder::with_x`], except that it provides a `Vec` of fresh `Ident`s to build with, rather than a single `Ident`.
    The provided `n` argument specifies the number of generated `Ident`s.
    */
    pub fn with_x_many<F>(n: usize, f: F) -> Self
    where F: FnOnce(Vec<Ident>) -> Self + 'static,
    {
        Self::new(move |igen| {
            let xs = igen.next_many(n);
            f(xs).build_with(igen)
        })
    }

    pub fn igen_many<F1,F2>(self, n: usize, f: F1) -> Self
    where
        F1: FnOnce(Self) -> F2 + 'static,
        F2: FnOnce(Vec<Ident>) -> Self,
    {
        Self::new(move |igen| {
            let m = self.build_with(igen);
            let xs = igen.next_many(n);
            f(Builder::lift(m))(xs).build_with(igen)
        })
    }

    /**
    `Builder::lift(m)` produces a `Builder`
    that will itself simply reproduce `m`.

    ```
    use ravenlang::{Builder, Comp, Ident, Val};

    let m: Comp = Comp::Return(vec![
        Val::var(Ident::new("x"))
    ]);

    assert!(
        m.clone() == 
            Builder::lift(m).build_no_context()
    );
    ```
    */
    pub fn lift(m: Comp) -> Self {
        let fun = Box::new(|igen: &mut IGen| {
            m.advance_igen(igen);
            m
        });
        Self{ fun }
    }

    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce(&mut IGen) -> Comp + 'static
    {
        Self{fun: Box::new(f)}
    }
    pub fn map<F>(self, f: F) -> Self
    where
        F: FnOnce(Comp) -> Comp + 'static
    {
        Self::new(|igen| {
            f(self.build_with(igen))
        })
    }
    pub fn bind<F>(self, f: F) -> Self
    where
        F: FnOnce(Comp) -> Self + 'static,
    {
        Self::new(|igen| {
            f(self.build_with(igen)).build_with(igen)
        })
    }
    pub fn bind_many<F>(bs: Vec<Self>, f: F) -> Self
    where
        F: FnOnce(Vec<Comp>) -> Self + 'static,
    {
        Self::new(|igen| {
            let cs = bs
                .into_iter()
                .map(|b| b.build_with(igen))
                .collect();
            f(cs).build_with(igen)
        })
    }
    pub fn return_<V: Into<Val>>(v: V) -> Self {
        Self::lift(Comp::return1(v))
    }
    pub fn return_thunk(b: Self) -> Self {
        Self::new(|igen| {
            let m = b.build_with(igen);
            Comp::return1(Val::thunk(&m))
        })
    }
    pub fn force<V: Into<Val>>(v: V) -> Self {
        Self::lift(Comp::force(v))
    }

    pub fn true_() -> Self {
        Self::return_(Val::true_())
    }
    pub fn false_() -> Self {
        Self::return_(Val::false_())
    }

    pub fn var<T: Into<Ident>>(i: T) -> Self {
        Self::return_(Val::into_var(i))
    }

    pub fn seq_ident<F1>(self, x: Ident, cont: F1) -> Self
    where
        F1: FnOnce(Val) -> Self + 'static,
    {
        Self::new(|igen: &mut IGen| {
            let m1 = self.build_with(igen);
            let m2 = cont(x.clone().val()).build_with(igen);
            Comp::seq(m1, x, m2)
        })
    }

    /**
    Sequence two `Builder`s, binding the first to a given [`Pattern`].

    In the following example, `b3` is equivalent to
    `let (a,b,_) = (x,y,z); a || b`.
    
    ```
    use ravenlang::{Builder, Pattern};

    let b1 = Builder::tuple([
        Builder::var("x"),
        Builder::var("y"),
        Builder::var("z"),
    ]);

    let p = Pattern::tuple([
        Pattern::atom("a"),
        Pattern::atom("b"),
        Pattern::NoBind
    ]);

    let b2 = Builder::var("a").or(Builder::var("b"));

    let b3 = b1.seq_pattern(p, b2);
    ```
    */
    pub fn seq_pattern(self, p: Pattern, cont: Self) -> Self
    {
        Self::new(|igen: &mut IGen| {
            let m1 = self.build_with(igen);
            Comp::BindN(
                BinderN::Seq(Box::new(m1)),
                vec![p],
                Box::new(cont.build_with(igen)),
            )
        })
    }

    /// ```m1.seq_igen(f)``` gives you `m1 to x. f(x)` in CBPV terms,
    /// but with a unique generated variable in place of `x`.
    pub fn seq_igen<F>(self, cont: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static
    {
        self.igen(|b||x| {
            b.seq_ident(x, cont)
        })
    }

    pub fn seq_many<F>(bxs: Vec<(Self, Ident)>, cont: F) -> Self
    where
        F: FnOnce(Vec<Val>) -> Self + 'static,
    {
        let mut bs = Vec::new();
        let mut xs = Vec::new();
        for (b,x) in bxs {
            bs.push(b);
            xs.push(x);
        }
        Self::bind_many(bs, |ms| {
            let vs = xs.clone()
                .into_iter()
                .map(|x| x.val())
                .collect();
            Self::bind(cont(vs), |m2| {
                Comp::seq1_many(ms, xs, m2).builder()
            })
        })
    }

    /// Same as `Builder::seq_igen`, but binds multiple `Builder`s to
    /// multiple generated variable names.
    pub fn seq_many_igen<Cs,F>(bs: Cs, cont: F) -> Self
    where
        Cs: Into<Vec<Self>> + 'static,
        F: FnOnce(Vec<Val>) -> Self + 'static,
    {
        Self::new(|igen: &mut IGen| {
            let ms: Vec<Comp> =
                bs.into().into_iter().map(|b| b.build_with(igen)).collect();
            let xs = igen.next_many(ms.len());
            let m2 =
                cont(xs.clone().into_iter().map(|x| x.val()).collect())
                .build_with(igen);
            Comp::seq1_many(ms, xs, m2)
        })
    }

    /// Create a function, using a freshly generated variable name. In
    /// fhe following example, `b` gives you a function equivalent to
    /// `|x: bool| (x,x)`, but with a unique name in place of `x`.
    ///
    /// ```
    /// use ravenlang::{Builder, VType};
    ///
    /// let b = Builder::fun_igen(VType::prop(), |x| {
    ///     Builder::tuple([
    ///         Builder::return_(x.clone()),
    ///         Builder::return_(x)
    ///     ])
    /// });
    /// ```
    pub fn fun_igen<F>(t: VType, cont: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        Self::new(|igen: &mut IGen| {
            let x = igen.next();
            let v = x.clone().val();
            Comp::Fun(vec![(x, Some(t))], Box::new(cont(v).build_with(igen)))
        })
    }

    /**
    This works like [`Builder::fun_igen`], but generate input
    variables for a sequence of types.
    */
    pub fn fun_many_igen<Ts,F>(ts: Ts, cont: F) -> Self
    where
        Ts: Into<Vec<VType>> + 'static,
        F: FnOnce(Vec<Val>) -> Self + 'static,
    {
        Self::new(|igen: &mut IGen| {
            let ts = ts.into();

            let xs = igen.next_many(ts.len());
            let vs = xs.clone().into_iter().map(|x| x.val()).collect();
            let xts = xs.into_iter().zip(ts).map(|(x,t)| (x,Some(t))).collect();
            Comp::Fun(xts, Box::new(cont(vs).build_with(igen)))
        })
    }

    /// `x.eq_ne(true, y)` gives you `x == y`.
    ///
    /// `x.eq_ne(false, y)` gives you `x != y`.
    pub fn eq_ne(self, pos: bool, other: Self) -> Self {
        self.seq_igen(move |x| {
             other.seq_igen(move |y| {
                Self::new(move |igen: &mut IGen| {
                    let x_result = igen.next();
                    Comp::eq_ne(
                        pos,
                        [x],
                        [y],
                        x_result.clone(),
                        Comp::return1(x_result)
                    )
                })
            })
        })
    }

    pub fn log_op<Bs: Into<Vec<Self>>>(op: LogOpN, bs: Bs) -> Builder {
        let mut bs: Vec<Self> = bs.into();
        Self::new(|igen: &mut IGen| {
            bs.reverse();
            let mut ms = Vec::new();
            for b in bs {
                ms.push(b.build_with(igen));
            }
            let xs = igen.next_many(ms.len());
            let vs = xs.clone().into_iter().map(|x| x.val()).collect();
            let y = igen.next();
            Comp::seq1_many(
                ms,
                xs,
                Comp::Bind1(
                    Binder1::LogOpN(op, vs),
                    y.clone(),
                    Box::new(Comp::return1(y)),
                )
            )
        })
    }

    /// `Builder::and_many([x,y,z])`
    /// gived you `x && y && z`
    pub fn and_many<Bs: Into<Vec<Self>>>(bs: Bs) -> Self {
        Self::log_op(LogOpN::And, bs)
    }

    /// `x.and(y)` gives you `x && y`.
    pub fn and<T: Into<Self>>(self, other: T) -> Self {
        Self::and_many([self, other.into()])
    }

    /// `Builder::or_many([x,y,z])`
    /// gives you `x || y || z`.
    pub fn or_many<Bs: Into<Vec<Self>>>(bs: Bs) -> Self {
        Self::log_op(LogOpN::Or, bs)
    }

    /// `x.or(y)` gives you `x || y`.
    pub fn or<T: Into<Self>>(self, other: T) -> Self {
        Self::or_many([self, other.into()])
    }

    /// `x.implies(y)` gives you `!x || y`.
    pub fn implies<T: Into<Self>>(self, other: T) -> Self {
        self.not().or(other)
    }

    /// `x.is_eq(y)`
    /// gives you `x == y`.
    pub fn is_eq<T: Into<Self>>(self, other: T) -> Self {
        self.eq_ne(true, other.into())
    }

    /// `x.is_ne(y)`
    /// gives you `x != y`.
    pub fn is_ne<T: Into<Self>>(self, other: T) -> Self {
        self.eq_ne(false, other.into())
    }

    /// `x.ite(y, z)` gives you `if x then { y } else { z }`.
    pub fn ite(self, then_branch: Self, else_branch: Self) -> Self {
        self.seq_igen(|v_cond| {
            then_branch.bind(|m_then| {
                else_branch.bind(|m_else| {
                    Self::lift(Comp::ite(v_cond, m_then, m_else))
                })
            })
        })
    }

    /// `mat` gives you a match statement.
    pub fn mat(self, arms: Vec<(MatchArm, Self)>) -> Self {
        let mut matchers = Vec::new();
        let mut comps = Vec::new();
        for (m,c) in arms {
            matchers.push(m);
            comps.push(c);
        }
        self.seq_igen(|v_target| {
            Self::bind_many(comps, |comps| {
                let comps = comps
                    .into_iter()
                    .map(|c| Box::new(c))
                    .collect::<Vec<_>>();
                let arms = matchers
                    .into_iter()
                    .zip(comps)
                    .collect();
                Self::lift(Comp::Match(v_target, arms))
            })
        })
    }

    /// `Builder::tuple([x, y])` gives you `(x,y)`.
    pub fn tuple<Bs>(bs: Bs) -> Self
    where
        Bs: Into<Vec<Self>> + 'static
    {
        Self::seq_many_igen(bs, |xs| {
            Self::return_(Val::Tuple(xs))
        })
    }

    /// `x.not()` gives you `!x`.
    pub fn not(self) -> Self {
        self.seq_igen(|x| Builder::new(|igen: &mut IGen| {
            let x_neg = igen.next();
            Comp::not(x, x_neg.clone(), Comp::return1(x_neg))
        }))
    }

    /// `m.flatten()` gives you `m to x. force x`, in CBPV
    /// terms. Basically, this and [`Builder::ret_thunk()`] are inverse
    /// operations.
    pub fn flatten(self) -> Self {
        self.seq_igen(|x_thunk| {
            Builder::lift(Comp::force(x_thunk))
        })
    }

    /// `m.ret_thunk()` gives you `return (thunk m)`, in CBPV terms.
    pub fn ret_thunk(self) -> Self {
        Self::new(|igen: &mut IGen| {
            Comp::Return(vec![Val::Thunk(Box::new(self.build_with(igen)))])
        })
    }

    /** 
    Wrap the given `Builder` in a quantifier, using the given
    variable names and types.

    The following example first constructs `x && y` and then wraps it
    into `forall(|x: bool, y: bool| { x && y })`.

    ```
    use ravenlang::{Builder, Ident, Quantifier, VType};

    let b1 = Builder::var("x").and(Builder::var("y"));
    let b2 = b1.into_quantifier(
        Quantifier::Forall,
        [(Ident::new("x"), VType::prop()),
         (Ident::new("y"), VType::prop())
        ]
    );
    ```
    */
    pub fn into_quantifier<Xs>(self, q: Quantifier, xs: Xs) -> Self
    where
        Xs: Into<Vec<(Ident,VType)>> + 'static,
    {
        Self::new(move |igen: &mut IGen| {
            let x_result = igen.next();
            Comp::quant_many(
                q,
                xs.into(),
                self.build_with(igen),
                x_result.clone(),
                Comp::return1(x_result),
            )
        })
    }

    /** 
    The following example gives `exists(|x: bool| x == x)`, but
    with a unique generated variable name in place of `x`.

    ```
    use ravenlang::{Builder, Quantifier, VType};

    let b = Builder::quantify(
        Quantifier::Exists,
        VType::prop(),
        |x| { Builder::return_(x.clone())
              .is_eq(Builder::return_(x)) }
    );
    ```
    */
    pub fn quantify<F>(q: Quantifier, t_q: VType, f: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        let f = |mut vs: Vec<Val>| f(vs.pop().unwrap());
        Self::quantify_many(q, [t_q], f)
    }

    /// Just like [`Builder::quantify`], but generates a sequence of
    /// unique variables names for a sequence of quantified types.
    pub fn quantify_many<Ts,F>(q: Quantifier, ts_q: Ts, f: F) -> Self
    where
        F: FnOnce(Vec<Val>) -> Self + 'static,
        Ts: Into<Vec<VType>> + 'static,
    {
        let ts_q: Vec<VType> = ts_q.into();
        Self::with_x_many(ts_q.len(), move |xs_q| {
            let qs: Vec<(Ident,VType)> =
                xs_q.clone().into_iter().zip(ts_q).collect();
            let vs_q = xs_q.into_iter().map(|x| x.val()).collect();
            let body = f(vs_q);
            body.into_quantifier(q, qs)
        })
    }

    pub fn forall<F>(t_q: VType, f: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        Self::quantify(Quantifier::Forall, t_q, f)
    }

    pub fn forall_many<Ts,F>(ts_q: Ts, f: F) -> Self
    where
        F: FnOnce(Vec<Val>) -> Self + 'static,
        Ts: Into<Vec<VType>> + 'static,
    {
        Self::quantify_many(Quantifier::Forall, ts_q, f)
    }

    pub fn exists<F>(t_q: VType, f: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        Self::quantify(Quantifier::Exists, t_q, f)
    }

    pub fn exists_many<Ts,F>(ts_q: Ts, f: F) -> Self
    where
        F: FnOnce(Vec<Val>) -> Self + 'static,
        Ts: Into<Vec<VType>> + 'static,
    {
        Self::quantify_many(Quantifier::Exists, ts_q, f)
    }

    /** 
    Wrap the given builder in a function, which takes the given
    types as arguments, bound to the given variable names.

    The following example first constructs `x && y` and then wraps it
    into `|x: bool, y: bool| { x && y }`.

    ```
    use ravenlang::{Builder, Ident, VType};

    let b1 = Builder::var("x").and(Builder::var("y"));
    let b2 = b1.into_fun(
        [(Ident::new("x"), VType::prop()),
         (Ident::new("y"), VType::prop())
        ]
    );
    ```
    */
    pub fn into_fun<Xs>(self, xs: Xs) -> Self
    where
        Xs: Into<Vec<(Ident,VType)>> + 'static,
    {
        let xs: Vec<(Ident,VType)> = xs.into();
        let xs: Vec<(Ident,Option<VType>)> = xs
            .into_iter()
            .map(|(i,t)| (i, Some(t)))
            .collect();
        Self::new(move |igen: &mut IGen| {
            Comp::Fun(xs.into(), Box::new(self.build_with(igen)))
        })
    }

    pub fn apply_v<Vs>(self, vs: Vs) -> Self
    where
        Vs: Into<Vec<Val>> + 'static
    {
        Self::new(|igen: &mut IGen| {
            Comp::apply(self.build_with(igen), Vec::new(), vs)
        })
    }

    pub fn apply<Bs>(self, bs: Bs) -> Self
    where
        Bs: Into<Vec<Self>> + 'static,
    {
        Self::seq_many_igen(bs, |xs| {
            self.apply_v(xs)
        })
    }

    pub fn apply_rt(self, vs: Vec<Val>) -> Self {
        Self::new(|igen: &mut IGen| {
            let m = self.build_with(igen);
            let x_thunk = igen.next();
            Comp::seq(
                m,
                x_thunk.clone(),
                Comp::apply(Comp::force(x_thunk), Vec::new(), vs),
            )
        })
    }
}
