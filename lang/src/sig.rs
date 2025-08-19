use crate::cbpv::Comp;
use std::collections::HashMap;
use std::collections::HashSet;

/// A sort is a base type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    Prop,
    UI(String),
}

impl Sort {
    pub fn prop() -> Self { Self::Prop }
    pub fn string() -> Self { Self::UI(format!("String")) }
    pub fn nat() -> Self { Self::UI(format!("Nat")) }
    pub fn set() -> Self { Self::UI(format!("Set")) }
    pub fn ui<T: ToString>(t: T) -> Self { Self::UI(t.to_string()) }
    pub fn as_string(&self) -> String {
        match self {
            Self::Prop => format!("Bool"),
            Self::UI(s) => format!("s_{}", s),
        }
    }
    // This one displays the sort as it would appear in the surface
    // language.
    pub fn render(&self) -> String {
        match self {
            Self::Prop => format!("bool"),
            Self::UI(s) => format!("{}", s),
        }
    }
    pub fn unwrap_ui(self) -> String {
        match self {
            Self::UI(s) => s,
            _ => panic!("Tried to unwrap non-ui sort"),
        }
    }
}

/// A VType is a base type or a tuple
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VType {
    Atom(Sort),
    Tuple(Vec<VType>),
    Thunk(Box<CType>),
}

impl VType {
    pub fn contains_prop(&self) -> bool {
        match self {
            VType::Atom(s) => *s == Sort::prop(),
            VType::Tuple(vs) => vs.iter().any(|t| t.contains_prop()),
            vt => panic!("no contains_prop for {:?}", vt),
        }
    }
    pub fn contains_ui(&self, s: &str) -> bool {
        match self {
            VType::Atom(Sort::UI(s1)) => s == s1,
            VType::Atom(Sort::Prop) => false,
            VType::Tuple(ts) => {
                ts.iter().map(|t| t.contains_ui(s)).any(|r| r)
            }
            VType::Thunk(ct) => ct.contains_ui(s),
        }
    }
    pub fn expand_aliases(self, aliases: &HashMap<String,Self>) -> Self {
        match self {
            VType::Atom(Sort::UI(s)) => match aliases.get(&s) {
                Some(t) => t.clone(),
                None => VType::Atom(Sort::UI(s)),
            }
            VType::Atom(Sort::Prop) => VType::Atom(Sort::Prop),
            VType::Tuple(ts) => VType::Tuple(
                ts.into_iter().map(|t| t.expand_aliases(aliases)).collect()
            ),
            VType::Thunk(ct) =>
                VType::Thunk(Box::new(ct.expand_aliases(aliases))),
        }
    }
    pub fn render(&self) -> String {
        assert!(
            !self.contains_thunk(),
            "cannot render vtype that contains thunk: {:?}",
            self,
        );
        match self.clone() {
            VType::Atom(s) => s.render(),
            VType::Tuple(ts) => {
                let mut out = String::from("(");
                let mut first = true;
                for t in ts {
                    if first {
                        first = false;
                        out.push_str(&t.render());
                    } else {
                        out.push_str(&format!(", {}", t.render()));
                    }
                }
                out.push_str(")");
                out
            }
            _ => unreachable!(),
        }
    }
    pub fn contains_thunk(&self) -> bool {
        match self {
            VType::Atom(_s) => false,
            VType::Tuple(ts) => {
                for t in ts {
                    if t.contains_thunk() {
                        return true
                    }
                }
                false
            }
            VType::Thunk(_ct) => true,
        }
    }
    pub fn unwrap_atom(self) -> Result<Sort,Self> {
        match self {
            VType::Atom(s) => Ok(s),
            t => Err(t),
        }
    }
    pub fn flatten(self) -> Vec<Self> {
        let mut out = Vec::new();
        match self {
            Self::Atom(s) => {
                out.push(Self::Atom(s));
            }
            Self::Tuple(ts) => {
                for t in ts {
                    let mut v = t.flatten();
                    out.append(&mut v);
                }
            }
            vt => panic!("Can't flatten {:?}", vt),
        }
        out
    }
    pub fn flatten_many(ts: Vec<Self>) -> Vec<Self> {
        let mut out = Vec::new();
        for t in ts {
            out.append(&mut t.flatten());
        }
        out
    }

    pub fn tuple<V: Into<Vec<VType>>>(v: V) -> Self {
        Self::Tuple(v.into())
    }

    pub fn ui<T: ToString>(s: T) -> Self {
        Self::Atom(Sort::ui(s))
    }

    pub fn unit() -> Self {
        Self::Tuple(Vec::new())
    }

    pub fn fun_v<V: Into<Vec<VType>>>(inputs: V, output: VType) -> Self {
        Self::Thunk(Box::new(CType::Fun(
            inputs.into(),
            Box::new(CType::Return(output)),
        )))
    }
    pub fn unwrap_fun_v(self) -> Option<(Vec<VType>, VType)> {
        match self {
            Self::Thunk(ct) => match *ct {
                CType::Fun(vts, ct) => match *ct {
                    CType::Return(vt) => Some((vts, vt)),
                    _ => None,
                }
                _ => None,
            }
            _ => None,
        }
    }
    pub fn prop() -> Self {
        Self::Atom(Sort::prop())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CType {
    Fun(Vec<VType>, Box<CType>),
    Return(VType),
}

impl CType {
    pub fn return_prop() -> Self {
        Self::Return(VType::prop())
    }
    pub fn fun(ts: Vec<VType>, m: CType) -> Self {
        CType::Fun(ts, Box::new(m))
    }
    pub fn unwrap_fun_v(self) -> Option<(Vec<VType>, VType)> {
        match self {
            CType::Return(v) => v.unwrap_fun_v(),
            _ => None,
        }
    }
    pub fn expand_aliases(self, aliases: &HashMap<String,VType>) -> Self {
        match self {
            Self::Fun(vts, ct) => Self::fun(
                vts.into_iter().map(|t| t.expand_aliases(aliases)).collect(),
                ct.expand_aliases(aliases),
            ),
            Self::Return(vt) => Self::Return(vt.expand_aliases(aliases)),
        }
    }
    pub fn contains_ui(&self, s: &str) -> bool {
        match self {
            Self::Fun(vts, ct) => {
                let in_args = vts.iter().map(|t| t.contains_ui(s)).any(|r| r);
                let in_body = ct.contains_ui(s);
                in_args || in_body
            }
            Self::Return(vt) => vt.contains_ui(s),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstOp {
    pub vtype: VType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecOp {
    pub inputs: Vec<VType>,
    pub output: VType,
    pub axiom: Comp,
    pub def: Comp,
}

impl RecOp {
    pub fn as_fun_op(self) -> FunOp {
        FunOp {
            inputs: self.inputs,
            output: self.output,
            axioms: vec![self.axiom],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunOp {
    pub inputs: Vec<VType>,
    pub output: VType,
    pub axioms: Vec<Comp>,
}

impl FunOp {
    pub fn annotation_type(&self) -> CType {
        CType::Return(VType::fun_v(
            self.inputs.clone(),
            VType::fun_v(
                [self.output.clone()],
                VType::prop(),
            )
        ))
    }
}

pub fn rel_abs_name<S: ToString>(s: S) -> String {
    format!("relabs_{}", s.to_string())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredOp {
    pub inputs: Vec<VType>,
    pub axioms: Vec<Comp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredSymbol {
    pub inputs: Vec<VType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Const(ConstOp),
    Direct(Comp),
    Fun(FunOp),
    Pred(PredOp),
    Rec(RecOp),
    Symbol(PredSymbol),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sig {
    pub sorts: HashSet<String>,
    pub type_aliases: HashMap<String,VType>,
    pub ops: Vec<(String, Op)>,
    // Note that axioms here should already be in normal form.
    pub axioms: Vec<Comp>,
}

impl Sig {
    pub fn empty() -> Sig {
        Sig {
            sorts: HashSet::new(),
            type_aliases: HashMap::new(),
            ops: Vec::new(),
            axioms: Vec::new(),
        }
    }
    pub fn all_op_names(&self) -> Vec<String> {
        self.ops_map().clone().into_iter().map(|(k,_)| k).collect()
    }
    pub fn ops_map(&self) -> HashMap<String, Op> {
        let mut m = HashMap::new();
        for (n,o) in self.ops.clone() {
            m.insert(n,o);
        }
        m
    }
    pub fn ops_vec(&self) -> Vec<(String, Op)> {
        self.ops.clone()
    }
    pub fn add_sort<S: ToString>(&mut self, s: S) {
        self.sorts.insert(s.to_string());
    }
    pub fn add_alias<S1: ToString>(&mut self, s: S1, t: VType) {
        let s = s.to_string();
        assert!(
            !t.contains_ui(&s),
            "Recursive type alias \"{}\" is not allowed",
            s,
        );
        assert!(t.validate(self) == Ok(()));
        self.type_aliases.insert(s, t);
    }
    pub fn add_constant<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        sort: S2,
    ) {
        assert!(self.sorts.contains(&sort.to_string()));
        self.ops.push((
            name.to_string(),
            Op::Const(ConstOp{
                vtype: VType::ui(sort.to_string()),
            }))
        );
    }
    pub fn add_relation<S1: ToString, S2: ToString, const N: usize>(
        &mut self,
        name: S1,
        inputs: [S2; N],
    ) {
        for i in inputs.iter() {
            assert!(
                self.sorts.contains(&i.to_string())
                    || self.type_aliases.get(&i.to_string()).is_some(),
                "{} is not a declared sort",
                i.to_string(),
            );
        }
        let op = Op::Symbol(PredSymbol{
            inputs: inputs
                .into_iter()
                .map(|s| VType::Atom(Sort::ui(s.to_string())).expand_aliases(&self.type_aliases))
                .collect(),
        });
        self.ops.push((name.to_string(), op));
    }
    pub fn add_relation_t<S1: ToString, const N: usize>(
        &mut self,
        name: S1,
        inputs: [VType; N],
    ) {
        for i in inputs.iter() {
            assert!(i.validate(self) == Ok(()));
        }
        let op = Op::Symbol(PredSymbol{
            inputs: inputs
                .into_iter()
                .map(|t| t.expand_aliases(&self.type_aliases))
                .collect(),
        });
        self.ops.push((name.to_string(), op));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn vtype_render1() {
        assert_eq!(
            &VType::unit().render(),
            "()",
        );
        assert_eq!(
            &VType::tuple([VType::ui("u32"), VType::ui("u32"), VType::prop()]).render(),
            "(u32, u32, bool)",
        );
        assert_eq!(
            &VType::tuple([
                VType::ui("u32"),
                VType::tuple([
                    VType::ui("Set_u32"),
                    VType::prop(),
                ]),
                VType::prop(),
            ]).render(),
            "(u32, (Set_u32, bool), bool)",
        );
    }
}
