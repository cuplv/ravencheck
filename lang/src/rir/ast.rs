//! # The AST for Raven IR (i.e. RIR)

use crate::sig::{OpCode, VType};
use crate::Ident;
use std::fmt;

impl Ident {
    pub fn val(self) -> Val {
        Val::var(self)
    }
    pub fn val_negative(self) -> Val {
        Val::var_negative(self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    LogTrue,
    LogFalse,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpMode {
    Const,
    RelAbs,
    ZeroArgAsConst(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Val {
    Literal(Literal),
    OpCode(OpMode, OpCode),
    Thunk(Box<Comp>),
    Tuple(Vec<Val>),
    /// (ident, types, path, is_positive)
    ///
    /// is_positive should only equal `false` when types and path are
    /// both empty.
    Var(Ident, Vec<VType>, Option<String>, bool),
}

impl Val {
    pub fn var(v: Ident) -> Self {
        Self::Var(v, Vec::new(), None, true)
    }
    pub fn into_var<T: Into<Ident>>(v: T) -> Self {
        Self::var(v.into())
    }
    pub fn var_negative(v: Ident) -> Self {
        Self::Var(v, Vec::new(), None, false)
    }
    pub fn thunk(c: &Comp) -> Self {
        Self::Thunk(Box::new(c.clone()))
    }
    pub fn true_() -> Self {
        Self::Literal(Literal::LogTrue)
    }
    pub fn false_() -> Self {
        Self::Literal(Literal::LogFalse)
    }
    pub fn from_bool(b: bool) -> Self {
        if b {
            Val::true_()
        } else {
            Val::false_()
        }
    }
    pub fn tuple(vs: Vec<Val>) -> Self {
        if vs.len() == 1 {
            // No such thing as a 1-tuple
            vs[0].clone()
        } else {
            Self::Tuple(vs)
        }
    }
    pub fn unit() -> Self {
        Self::Tuple(Vec::new())
    }
    pub fn op(OpCode{ident, types, path}: OpCode) -> Self {
        Self::Var(Ident::new(ident), types, path, true)
    }
    pub fn rel_abs(code: OpCode) -> Self {
        Self::OpCode(OpMode::RelAbs, code)
    }
    pub fn zero_arg_as_const(code: OpCode) -> Self {
        Self::OpCode(OpMode::ZeroArgAsConst(true), code)
    }
    pub fn ret(self) -> Comp {
        Comp::return1(self)
    }
    pub fn force(self) -> Comp {
        Comp::force(self)
    }
}

impl From<Ident> for Val {
    fn from(x: Ident) -> Self {
        x.val()
    }
}

impl OpCode {
    pub fn as_fun(self) -> Comp {
        Val::op(self).ret()
    }
    pub fn as_rel_abs(self) -> Val {
        Val::rel_abs(self)
    }
    pub fn as_zero_arg_as_const(self) -> Val {
        Val::zero_arg_as_const(self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HypotheticalCall {
    pub ident: String,
    pub tas: Vec<String>,
    pub inputs: Vec<String>,
    pub output: String,
}

impl HypotheticalCall {
    pub fn code(&self) -> OpCode {
        let ident = self.ident.clone();
        let types = self.tas.clone().into_iter().map(VType::ui).collect();
        OpCode{ ident, types, path: None }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    NoBind,
    Atom(Ident),
    Tuple(Vec<Pattern>),
}

impl Pattern {
    pub fn unwrap_vname(self) -> Result<Ident, String> {
        match self {
            Pattern::Atom(x) => Ok(x),
            p => Err(format!("Got complex pattern {:?} that should be a plain identifier", p)),
        }
    }
    pub fn unwrap_atom(self) -> Option<Ident> {
        match self {
            Pattern::NoBind => None,
            Pattern::Atom(x) => Some(x),
            Pattern::Tuple(_) => None,
        }
    }
    pub fn atom<T: Into<Ident>>(x: T) -> Self { Self::Atom(x.into()) }
    pub fn tuple<Ps: Into<Vec<Self>>>(ps: Ps) -> Self {
        Pattern::Tuple(ps.into())
    }
}

/// Computations that bind multiple variables for use in a body
/// computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderN {
    Call(OpCode, Vec<Val>),
    Seq(Box<Comp>),
}

/// A logical operator that takes zero or more arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LogOpN {
    Or,
    And,
    Pred(OpCode,bool),
}

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Exists,
    Forall,
}

impl Quantifier {
    pub fn invert(self) -> Self {
        match self {
            Self::Exists => Self::Forall,
            Self::Forall => Self::Exists,
        }
    }
}

/// Computations that bind a single variable for use in a body
/// computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Binder1 {
    Eq(bool, Vec<Val>, Vec<Val>),
    LogQuantifier(Quantifier, Vec<(Ident, VType)>, Box<Comp>),
    LogNot(Val),
    LogOpN(LogOpN, Vec<Val>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub code: OpCode,
    pub binders: Vec<Pattern>,
}

impl MatchArm {
    pub fn ty(&self) -> String {
        self.code.path.clone().unwrap()
    }
    pub fn constructor(&self) -> String {
        self.code.ident.clone()
    }
    pub fn select(
        con: &str,
        arms: Vec<(MatchArm, Box<Comp>)>
    ) -> Option<(Vec<Ident>,Comp)> {
        for (m,c) in arms.into_iter() {
            if con == &m.constructor() {
                let xs = m.binders
                    .into_iter()
                    .map(|p| {
                        p.unwrap_vname().unwrap()
                    })
                    .collect();
                return Some((xs, *c))
            }
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Comp {
    Apply(Box<Comp>, Vec<VType>, Vec<Val>),
    BindN(BinderN, Vec<Pattern>, Box<Comp>),
    Bind1(Binder1, Ident, Box<Comp>),
    Force(Val),
    Fun(Vec<(Ident, Option<VType>)>, Box<Comp>),
    Ite(Val, Box<Comp>, Box<Comp>),
    // Todo: we don't need the Box in the Match variant, since the
    // Comps are already in a Vec.
    Match(Val, Vec<(MatchArm, Box<Comp>)>),
    Return(Vec<Val>),
}

impl Comp {
    pub fn apply<Ts: Into<Vec<VType>>, Vs: Into<Vec<Val>>>(m: Self, targs: Ts, vs: Vs) -> Self {
        Self::Apply(Box::new(m), targs.into(), vs.into())
    }
    pub fn force<V: Into<Val>>(v: V) -> Self {
        Self::Force(v.into())
    }
    pub fn ite(cond: Val, then_b: Self, else_b: Self) -> Self {
        Self::Ite(cond, Box::new(then_b), Box::new(else_b))
    }
    pub fn return1<V: Into<Val>>(v: V) -> Self {
        Self::Return(vec![v.into()])
    }
    pub fn return_many<Vs: Into<Vec<Val>>>(vs: Vs) -> Self {
        Self::Return(vs.into())
    }
    pub fn seq<C1,C2>(m1: C1, x: Ident, m2: C2) -> Self
    where C1: Into<Self>, C2: Into<Self>
    {
        Self::BindN(
            BinderN::Seq(Box::new(m1.into())),
            vec![Pattern::Atom(x)],
            Box::new(m2.into()),
        )
    }
    pub fn seq1_many(ms: Vec<Self>, xs: Vec<Ident>, m2: Self) -> Self {
        assert!(
            ms.len() == xs.len(),
            "seq1_many with mismatched comp and name vecs"
        );
        let mut m = m2;
        for (m1, x1) in ms.into_iter().zip(xs) {
            m = Comp::BindN(
                BinderN::Seq(Box::new(m1)),
                vec![Pattern::Atom(x1)],
                Box::new(m)
            );
        }
        m
    }

    pub fn eq_ne<V1,V2,C>(pos: bool, v1: V1, v2: V2, x: Ident, m: C) -> Self
    where
        V1: Into<Vec<Val>>,
        V2: Into<Vec<Val>>,
        C: Into<Comp>,
    {
        Self::Bind1(
            Binder1::Eq(pos, v1.into(), v2.into()),
            x,
            Box::new(m.into())
        )
    }

    pub fn quant<C1: Into<Comp>, C2: Into<Comp>>(
        q: Quantifier,
        s: VType,
        x_quant: Ident,
        m_body: C1,
        x_result: Ident,
        m2: C2,
    ) -> Self {
        Self::Bind1(
            Binder1::LogQuantifier(q, vec![(x_quant,s)], Box::new(m_body.into())),
            x_result,
            Box::new(m2.into()),
        )
    }

    pub fn quant_many<C1: Into<Comp>, C2: Into<Comp>>(
        q: Quantifier,
        xs: Vec<(Ident,VType)>,
        m_body: C1,
        x_result: Ident,
        m2: C2,
    ) -> Self {
        Self::Bind1(
            Binder1::LogQuantifier(q, xs, Box::new(m_body.into())),
            x_result,
            Box::new(m2.into()),
        )
    }

    pub fn exists<C: Into<Comp>>(
        s: VType,
        x_quant: Ident,
        m_body: C,
        x_result: Ident,
        m2: C,
    ) -> Self {
        Self::quant(Quantifier::Exists, s, x_quant, m_body, x_result, m2)
    }

    pub fn forall<C: Into<Comp>>(
        s: VType,
        x_quant: Ident,
        m_body: C,
        x_result: Ident,
        m2: C,
    ) -> Self {
        Self::quant(Quantifier::Forall, s, x_quant, m_body, x_result, m2)
    }

    pub fn not<V: Into<Val>, C: Into<Comp>>(v: V, x: Ident, m: C) -> Self {
        Self::Bind1(Binder1::LogNot(v.into()), x, Box::new(m.into()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseName(Vec<String>);

impl fmt::Display for CaseName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::from("root");
        for seg in self.0.clone() {
            out.push_str(&format!("::{}", seg));
        }
        write!(f, "{}", out)
    }
}

impl CaseName {
    pub fn root() -> Self { CaseName(Vec::new()) }
    pub fn extend<T: ToString>(mut self, segment: T) -> Self {
        self.0.push(segment.to_string());
        self
    }
}

pub type Cases = Vec<(CaseName, Comp)>;
