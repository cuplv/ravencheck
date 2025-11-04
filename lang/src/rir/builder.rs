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
    pub fn build(self, igen: &mut IGen) -> Comp {
        (self.fun)(igen)
    }
    pub fn igen<F1,F2>(self, f: F1) -> Self
    where
        F1: FnOnce(Self) -> F2 + 'static,
        F2: FnOnce(Ident) -> Self,
    {
        Self::new(|igen| {
            let m = self.build(igen);
            let x = igen.next();
            f(Builder::lift(m))(x).build(igen)
        })
    }

    pub fn with_x<F>(f: F) -> Self
    where F: FnOnce(Ident) -> Self + 'static,
    {
        Self::new(move |igen| {
            let x = igen.next();
            f(x).build(igen)
        })
    }

    pub fn with_x_many<F>(n: usize, f: F) -> Self
    where F: FnOnce(Vec<Ident>) -> Self + 'static,
    {
        Self::new(move |igen| {
            let xs = igen.next_many(n);
            f(xs).build(igen)
        })
    }

    pub fn igen_many<F1,F2>(self, n: usize, f: F1) -> Self
    where
        F1: FnOnce(Self) -> F2 + 'static,
        F2: FnOnce(Vec<Ident>) -> Self,
    {
        Self::new(move |igen| {
            let m = self.build(igen);
            let xs = igen.next_many(n);
            f(Builder::lift(m))(xs).build(igen)
        })
    }
    pub fn lift(m: Comp) -> Self {
        Self{
            fun: Box::new(|_igen: &mut IGen| m)
        }
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
            f(self.build(igen))
        })
    }
    pub fn bind<F>(self, f: F) -> Self
    where
        F: FnOnce(Comp) -> Self + 'static,
    {
        Self::new(|igen| {
            f(self.build(igen)).build(igen)
        })
    }
    pub fn bind_many<F>(bs: Vec<Self>, f: F) -> Self
    where
        F: FnOnce(Vec<Comp>) -> Self + 'static,
    {
        Self::new(|igen| {
            let cs = bs
                .into_iter()
                .map(|b| b.build(igen))
                .collect();
            f(cs).build(igen)
        })
    }
    pub fn return_<V: Into<Val>>(v: V) -> Self {
        Self::lift(Comp::return1(v))
    }
    pub fn return_thunk(b: Self) -> Self {
        Self::new(|igen| {
            let m = b.build(igen);
            Comp::return1(Val::thunk(&m))
        })
    }
    pub fn force<V: Into<Val>>(v: V) -> Self {
        Self::lift(Comp::force(v))
    }
    pub fn seq<F1>(self, cont: F1) -> impl FnOnce(Ident) -> Self
    where
        F1: FnOnce(Val) -> Self + 'static,
    {
        |x|
        Self::new(|igen: &mut IGen| {
            let m1 = self.build(igen);
            let m2 = cont(x.clone().val()).build(igen);
            Comp::seq(m1, x, m2)
        })
    }
    pub fn seq_pat(self, cont: Self) -> impl FnOnce(Pattern) -> Self
    {
        |p|
        Self::new(|igen: &mut IGen| {
            let m1 = self.build(igen);
            Comp::BindN(
                BinderN::Seq(Box::new(m1)),
                vec![p],
                Box::new(cont.build(igen)),
            )
        })
    }
    pub fn seq_igen<F>(self, cont: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static
    {
        self.igen(|b||x| {
            b.seq(cont)(x)
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
    pub fn seq_many_igen<Cs,F>(bs: Cs, cont: F) -> Self
    where
        Cs: Into<Vec<Self>> + 'static,
        F: FnOnce(Vec<Val>) -> Self + 'static,
    {
        Self::new(|igen: &mut IGen| {
            let ms: Vec<Comp> =
                bs.into().into_iter().map(|b| b.build(igen)).collect();
            let xs = igen.next_many(ms.len());
            let m2 =
                cont(xs.clone().into_iter().map(|x| x.val()).collect())
                .build(igen);
            Comp::seq1_many(ms, xs, m2)
        })
    }

    pub fn fun_igen<F>(t: VType, cont: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        Self::new(|igen: &mut IGen| {
            let x = igen.next();
            let v = x.clone().val();
            Comp::Fun(vec![(x, Some(t))], Box::new(cont(v).build(igen)))
        })
    }

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
            Comp::Fun(xts, Box::new(cont(vs).build(igen)))
        })
    }

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
                ms.push(b.build(igen));
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

    pub fn and_many<Bs: Into<Vec<Self>>>(bs: Bs) -> Self {
        Self::log_op(LogOpN::And, bs)
    }

    pub fn and<T: Into<Self>>(self, other: T) -> Self {
        Self::and_many([self, other.into()])
    }

    pub fn or_many<Bs: Into<Vec<Self>>>(bs: Bs) -> Self {
        Self::log_op(LogOpN::Or, bs)
    }

    pub fn or<T: Into<Self>>(self, other: T) -> Self {
        Self::or_many([self, other.into()])
    }

    pub fn implies<T: Into<Self>>(self, other: T) -> Self {
        self.not().or(other)
    }

    pub fn is_eq<T: Into<Self>>(self, other: T) -> Self {
        self.eq_ne(true, other.into())
    }

    pub fn is_ne<T: Into<Self>>(self, other: T) -> Self {
        self.eq_ne(false, other.into())
    }

    pub fn ite(self, then_branch: Self, else_branch: Self) -> Self {
        self.seq_igen(|v_cond| {
            then_branch.bind(|m_then| {
                else_branch.bind(|m_else| {
                    Self::lift(Comp::ite(v_cond, m_then, m_else))
                })
            })
        })
    }

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

    pub fn tuple<Bs>(bs: Bs) -> Self
    where
        Bs: Into<Vec<Self>> + 'static
    {
        Self::seq_many_igen(bs, |xs| {
            Self::return_(Val::Tuple(xs))
        })
    }


    pub fn not(self) -> Self {
        self.seq_igen(|x| Builder::new(|igen: &mut IGen| {
            let x_neg = igen.next();
            Comp::not(x, x_neg.clone(), Comp::return1(x_neg))
        }))
    }
    pub fn flatten(self) -> Self {
        self.seq_igen(|x_thunk| {
            Builder::lift(Comp::force(x_thunk))
        })
    }
    pub fn ret_thunk(self) -> Self {
        Self::new(|igen: &mut IGen| {
            Comp::Return(vec![Val::Thunk(Box::new(self.build(igen)))])
        })
    }

    pub fn quant<Xs>(self, q: Quantifier, xs: Xs) -> Self
    where
        Xs: Into<Vec<(Ident,VType)>> + 'static,
    {
        Self::new(move |igen: &mut IGen| {
            let x_result = igen.next();
            Comp::quant_many(
                q,
                xs.into(),
                self.build(igen),
                x_result.clone(),
                Comp::return1(x_result),
            )
        })
    }

    pub fn quantify<F>(q: Quantifier, t_q: VType, f: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        let f = |mut vs: Vec<Val>| f(vs.pop().unwrap());
        Self::quantify_many(q, [t_q], f)
    }

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
            body.quant(q, qs)
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

    pub fn fun<Xs>(self, xs: Xs) -> Self
    where
        Xs: Into<Vec<(Ident,Option<VType>)>> + 'static,
    {
        Self::new(move |igen: &mut IGen| {
            Comp::Fun(xs.into(), Box::new(self.build(igen)))
        })
    }

    pub fn apply_v<Vs>(self, vs: Vs) -> Self
    where
        Vs: Into<Vec<Val>> + 'static
    {
        Self::new(|igen: &mut IGen| {
            Comp::apply(self.build(igen), Vec::new(), vs)
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
            let m = self.build(igen);
            let x_thunk = igen.next();
            Comp::seq(
                m,
                x_thunk.clone(),
                Comp::apply(Comp::force(x_thunk), Vec::new(), vs),
            )
        })
    }
}
