use crate::sig::VType;
use crate::vname::VName;
use crate::gen::Gen;
use crate::cbpv::{Binder1, BinderN, Comp, LogOpN, Pattern, Quantifier, Val};

pub struct Builder {
    fun: Box<dyn FnOnce(&mut Gen) -> Comp>,
}

impl Comp {
    pub fn builder(self) -> Builder {
        Builder{
            fun: Box::new(|_gen: &mut Gen| self)
        }
    }
}

impl Into<Builder> for Comp {
    fn into(self) -> Builder {
        self.builder()
    }
}

impl Builder {
    pub fn build(self, gen: &mut Gen) -> Comp {
        (self.fun)(gen)
    }
    pub fn gen<F1,F2>(self, f: F1) -> Self
    where
        F1: FnOnce(Self) -> F2 + 'static,
        F2: FnOnce(VName) -> Self,
    {
        Self::new(|gen| {
            let m = self.build(gen);
            let x = gen.next();
            f(Builder::lift(m))(x).build(gen)
        })
    }
    pub fn gen_many<F1,F2>(self, n: usize, f: F1) -> Self
    where
        F1: FnOnce(Self) -> F2 + 'static,
        F2: FnOnce(Vec<VName>) -> Self,
    {
        Self::new(move |gen| {
            let m = self.build(gen);
            let xs = gen.next_many(n);
            f(Builder::lift(m))(xs).build(gen)
        })
    }
    pub fn lift(m: Comp) -> Self {
        Self{
            fun: Box::new(|_gen: &mut Gen| m)
        }
    }
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce(&mut Gen) -> Comp + 'static
    {
        Self{fun: Box::new(f)}
    }
    pub fn bind<F>(self, f: F) -> Self
    where
        F: FnOnce(Comp) -> Self + 'static,
    {
        Self::new(|gen| {
            f(self.build(gen)).build(gen)
        })
    }
    pub fn return_<V: Into<Val>>(v: V) -> Self {
        Self::lift(Comp::return1(v))
    }
    pub fn return_thunk(b: Self) -> Self {
        Self::new(|gen| {
            let m = b.build(gen);
            Comp::return1(Val::thunk(&m))
        })
    }
    pub fn force<V: Into<Val>>(v: V) -> Self {
        Self::lift(Comp::force(v))
    }
    pub fn seq<F1>(self, cont: F1) -> impl FnOnce(VName) -> Self
    where
        F1: FnOnce(Val) -> Self + 'static,
    {
        |x|
        Self::new(|gen: &mut Gen| {
            let m1 = self.build(gen);
            let m2 = cont(x.clone().val()).build(gen);
            Comp::seq(m1, x, m2)
        })
    }
    pub fn seq_pat(self, cont: Self) -> impl FnOnce(Pattern) -> Self
    {
        |p|
        Self::new(|gen: &mut Gen| {
            let m1 = self.build(gen);
            Comp::BindN(
                BinderN::Seq(Box::new(m1)),
                vec![p],
                Box::new(cont.build(gen)),
            )
        })
    }
    pub fn seq_gen<F>(self, cont: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static
    {
        self.gen(|b||x| {
            b.seq(cont)(x)
        })
    }
    pub fn seq_many_gen<Cs,F>(bs: Cs, cont: F) -> Self
    where
        Cs: Into<Vec<Self>> + 'static,
        F: FnOnce(Vec<Val>) -> Self + 'static,
    {
        Self::new(|gen: &mut Gen| {
            let ms: Vec<Comp> =
                bs.into().into_iter().map(|b| b.build(gen)).collect();
            let xs = gen.next_many(ms.len());
            let m2 =
                cont(xs.clone().into_iter().map(|x| x.val()).collect())
                .build(gen);
            Comp::seq1_many(ms, xs, m2)
        })
    }

    pub fn fun_gen<F>(t: VType, cont: F) -> Self
    where
        F: FnOnce(Val) -> Self + 'static,
    {
        Self::new(|vgen: &mut Gen| {
            let x = vgen.next();
            let v = x.clone().val();
            Comp::Fun(vec![(x, Some(t))], Box::new(cont(v).build(vgen)))
        })
    }

    pub fn fun_many_gen<Ts,F>(ts: Ts, cont: F) -> Self
    where
        Ts: Into<Vec<VType>> + 'static,
        F: FnOnce(Vec<Val>) -> Self + 'static,
    {
        Self::new(|vgen: &mut Gen| {
            let ts = ts.into();

            let xs = vgen.next_many(ts.len());
            let vs = xs.clone().into_iter().map(|x| x.val()).collect();
            let xts = xs.into_iter().zip(ts).map(|(x,t)| (x,Some(t))).collect();
            Comp::Fun(xts, Box::new(cont(vs).build(vgen)))
        })
    }

    pub fn eq_ne(self, pos: bool, other: Self) -> Self {
        self.seq_gen(move |x| {
             other.seq_gen(move |y| {
                Self::new(move |gen: &mut Gen| {
                    let x_result = gen.next();
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
        Self::new(|gen: &mut Gen| {
            bs.reverse();
            let mut ms = Vec::new();
            for b in bs {
                ms.push(b.build(gen));
            }
            let xs = gen.next_many(ms.len());
            let vs = xs.clone().into_iter().map(|x| x.val()).collect();
            let y = gen.next();
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

    pub fn ite(self, then_branch: Self, else_branch: Self) -> Self {
        self.seq_gen(|v_cond| {
            then_branch.bind(|m_then| {
                else_branch.bind(|m_else| {
                    Self::lift(Comp::ite(v_cond, m_then, m_else))
                })
            })
        })
    }

    pub fn tuple<Bs>(bs: Bs) -> Self
    where
        Bs: Into<Vec<Self>> + 'static
    {
        Self::seq_many_gen(bs, |xs| {
            Self::return_(Val::Tuple(xs))
        })
    }


    pub fn not(self) -> Self {
        self.seq_gen(|x| Builder::new(|gen: &mut Gen| {
            let x_neg = gen.next();
            Comp::not(x, x_neg.clone(), Comp::return1(x_neg))
        }))
    }
    pub fn flatten(self) -> Self {
        self.seq_gen(|x_thunk| {
            Builder::lift(Comp::force(x_thunk))
        })
    }
    pub fn ret_thunk(self) -> Self {
        Self::new(|vgen: &mut Gen| {
            Comp::Return(vec![Val::Thunk(Box::new(self.build(vgen)))])
        })
    }

    pub fn quant<Xs>(self, q: Quantifier, xs: Xs) -> Self
    where
        Xs: Into<Vec<(VName,VType)>> + 'static,
    {
        Self::new(move |gen: &mut Gen| {
            let x_result = gen.next();
            Comp::quant_many(
                q,
                xs.into(),
                self.build(gen),
                x_result.clone(),
                Comp::return1(x_result),
            )
        })
    }

    pub fn fun<Xs>(self, xs: Xs) -> Self
    where
        Xs: Into<Vec<(VName,Option<VType>)>> + 'static,
    {
        Self::new(move |gen: &mut Gen| {
            Comp::Fun(xs.into(), Box::new(self.build(gen)))
        })
    }

    pub fn apply_v<Vs>(self, vs: Vs) -> Self
    where
        Vs: Into<Vec<Val>> + 'static
    {
        Self::new(|gen: &mut Gen| {
            Comp::apply(self.build(gen), vs)
        })
    }

    pub fn apply<Bs>(self, bs: Bs) -> Self
    where
        Bs: Into<Vec<Self>> + 'static,
    {
        Self::seq_many_gen(bs, |xs| {
            self.apply_v(xs)
        })
    }

    pub fn apply_rt(self, vs: Vec<Val>) -> Self {
        Self::new(|gen: &mut Gen| {
            let m = self.build(gen);
            let x_thunk = gen.next();
            Comp::seq(
                m,
                x_thunk.clone(),
                Comp::apply(Comp::force(x_thunk), vs),
            )
        })
    }
}
