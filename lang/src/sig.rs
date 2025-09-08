use crate::cbpv::Comp;
use std::collections::HashMap;
use std::fmt;

// /// A sort is a base type
// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum Sort {
//     Prop,
//     UI(String),
// }

// impl Sort {
//     pub fn prop() -> Self { Self::Prop }
//     pub fn string() -> Self { Self::UI(format!("String")) }
//     pub fn nat() -> Self { Self::UI(format!("Nat")) }
//     pub fn set() -> Self { Self::UI(format!("Set")) }
//     pub fn ui<T: ToString>(t: T) -> Self { Self::UI(t.to_string()) }
//     pub fn as_string(&self) -> String {
//         match self {
//             Self::Prop => format!("Bool"),
//             Self::UI(s) => format!("s_{}", s),
//         }
//     }
//     // This one displays the sort as it would appear in the surface
//     // language.
//     pub fn render(&self) -> String {
//         match self {
//             Self::Prop => format!("bool"),
//             Self::UI(s) => format!("{}", s),
//         }
//     }
//     pub fn unwrap_ui(self) -> String {
//         match self {
//             Self::UI(s) => s,
//             _ => panic!("Tried to unwrap non-ui sort"),
//         }
//     }
// }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OpCode {
    pub ident: String,
    pub types: Vec<VType>,
}

impl fmt::Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{}", &self.ident);
        // write!(f, "{}::<", &self.ident)?;
        if self.types.len() == 1 {
            s.push_str(&format!("::<{}>", &self.types[0].render()));
            // write!(f, "{}>", &self.types[0].render())
        } else if self.types.len() > 1 {
            s.push_str(&format!("::<"));
            let mut first = true;
            for t in &self.types {
                if first {
                    s.push_str(&format!("{}", t.render()));
                    // write!(f, "{}", t.render())?;
                    first = false;
                } else {
                    s.push_str(&format!(",{}", t.render()));
                    // write!(f, ",{}", t.render())?;
                }
            }
        }
        write!(f, "{}", s)
    }
}

/// A BType is a base type, which can be represented directly by a
/// sort.
///
/// Although BTypes can contain VTypes, they should never contain
/// Thunks.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BType {
    Prop,
    UI(String, Vec<VType>),
}

impl fmt::Display for BType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.render())
    }
}

impl BType {
    pub fn prop() -> Self { Self::Prop }
    pub fn ui<S: ToString>(s: S) -> Self {
        assert!(
            &s.to_string() != "bool",
            "\"bool\" should not be used as an uninterpreted type name."
        );
        Self::UI(s.to_string(), Vec::new())
    }
    pub fn ui_args<S: ToString>(s: S, args: Vec<VType>) -> Self {
        assert!(
            &s.to_string() != "bool",
            "\"bool\" should not be used as an uninterpreted type name."
        );
        assert!(
            args.iter().all(|t| !t.contains_thunk()),
            "type arguments to \"{}\" should not contain thunks",
            s.to_string(),
        );
        Self::UI(s.to_string(), args)
    }
    pub fn render(&self) -> String {
        match self {
            BType::Prop => format!("bool"),
            BType::UI(name, args) if args.len() == 0 => {
                format!("{}", name)
            }
            BType::UI(name, args) => {
                let mut out = format!("{}<", name);
                let mut first = true;
                for t in args {
                    if first {
                        first = false;
                        out.push_str(&t.render());
                    } else {
                        out.push_str(&format!(", {}", t.render()));
                    }
                }
                out.push_str(">");
                out
            }
        }
    }
    pub fn contains_prop(&self) -> bool {
        match self {
            BType::Prop => true,
            BType::UI(_, args) => args.iter().any(|t| t.contains_prop()),
        }
    }
    pub fn contains_ui(&self, name: &str) -> bool {
        match self {
            BType::Prop => false,
            BType::UI(n, args) => {
                n == name || args.iter().any(|t| t.contains_ui(name))
            }
        }
    }
    pub fn contains_thunk(&self) -> bool {
        match self {
            BType::Prop => false,
            BType::UI(_, args) => args.iter().any(|t| t.contains_thunk()),
        }
    }
    pub fn expand_aliases(self, aliases: &HashMap<String,VType>) -> VType {
        match self {
            BType::Prop => VType::Base(BType::Prop),
            BType::UI(s, args) => match aliases.get(&s) {
                Some(t) => {
                    assert!(args.len() == 0, "Aliases must have zero arity, but {} with arity {} was aliased.", s, args.len());
                    t.clone()
                }
                None => VType::Base(BType::UI(
                    s,
                    args.into_iter().map(|t| t.expand_aliases(aliases)).collect(),
                )),
            }
        }
    }
    pub fn get_ta(self) -> Option<String> {
        match self {
            BType::UI(name,args) if args.len() == 0 => {
                Some(name)
            }
            _ => None,
        }
    }
}

/// A VType is a base type or a tuple
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VType {
    Base(BType),
    Tuple(Vec<VType>),
    Thunk(Box<CType>),
}

impl VType {
    pub fn contains_prop(&self) -> bool {
        match self {
            VType::Base(t) => t.contains_prop(),
            VType::Tuple(vs) => vs.iter().any(|t| t.contains_prop()),
            vt => panic!("no contains_prop for {:?}", vt),
        }
    }
    pub fn contains_ui(&self, s: &str) -> bool {
        match self {
            VType::Base(t) => t.contains_ui(s),
            VType::Tuple(ts) => {
                ts.iter().map(|t| t.contains_ui(s)).any(|r| r)
            }
            VType::Thunk(ct) => ct.contains_ui(s),
        }
    }
    pub fn expand_aliases(self, aliases: &HashMap<String,Self>) -> Self {
        match self {
            VType::Base(t) => t.expand_aliases(aliases),
            VType::Tuple(ts) => VType::Tuple(
                ts.into_iter().map(|t| t.expand_aliases(aliases)).collect()
            ),
            VType::Thunk(ct) =>
                VType::Thunk(Box::new(ct.expand_aliases(aliases))),
        }
    }
    pub fn render(&self) -> String {
        match self.clone() {
            VType::Base(t) => t.render(),
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
            VType::Thunk(c) => format!("Thunk({})", c.render()),
        }
    }
    pub fn contains_thunk(&self) -> bool {
        match self {
            VType::Base(t) => t.contains_thunk(),
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
    pub fn unwrap_base(self) -> Result<BType,Self> {
        match self {
            VType::Base(t) => Ok(t),
            t => Err(t),
        }
    }
    pub fn flatten(self) -> Vec<Self> {
        let mut out = Vec::new();
        match self {
            Self::Base(t) => {
                out.push(Self::Base(t));
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
        Self::Base(BType::ui(s))
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
        Self::Base(BType::prop())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CType {
    Fun(Vec<VType>, Box<CType>),
    Return(VType),
}

impl CType {
    pub fn render(&self) -> String {
        match self {
            Self::Fun(vs, c) => {
                let mut s: String = format!("Fn(");
                let mut first = true;
                for t in vs {
                    if first {
                        s.push_str(&format!("{}", t.render()));
                        first = false;
                    } else {
                        s.push_str(&format!(",{}", t.render()));
                    }
                }
                s.push_str(&format!(") -> {}", c.render()));
                s
            }
            Self::Return(vt) => format!("Return({})", vt.render()),
        }
    }
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
    pub axioms: Vec<Comp>,
    pub def: Comp,
}

impl RecOp {
    pub fn as_fun_op(self) -> FunOp {
        FunOp {
            inputs: self.inputs,
            output: self.output,
            axioms: self.axioms,
        }
    }

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
pub struct Axiom {
    pub tas: Vec<String>,
    pub inst_rules: Vec<(BType,VType)>,
    pub body: Comp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sig {
    pub sorts: HashMap<String,usize>,
    pub type_aliases: HashMap<String,VType>,
    // The Vec<String> is the list of type parameters, which act as
    // aliases on the types in the Op.
    pub ops: Vec<(String, Vec<String>, Op)>,
    // Note that axioms here should already be in normal form.
    pub axioms: Vec<Axiom>,
}

impl Sig {
    pub fn empty() -> Sig {
        Sig {
            sorts: HashMap::new(),
            type_aliases: HashMap::new(),
            ops: Vec::new(),
            axioms: Vec::new(),
        }
    }
    pub fn get_op(&self, s: &str) -> Option<(&Vec<String>, &Op)> {
        for (name, tas, op) in self.ops.iter() {
            if name == s {
                return Some((tas, op))
            }
        }
        None
    }
    pub fn sort_arity(&self, s: &str) -> Option<usize> {
        self.sorts.get(s).copied()
    }
    pub fn all_op_names(&self) -> Vec<String> {
        self.ops_map().clone().into_iter().map(|(k,_)| k).collect()
    }
    pub fn ops_map(&self) -> HashMap<String, (Vec<String>,Op)> {
        let mut m = HashMap::new();
        for (n,args,o) in self.ops.clone() {
            m.insert(n,(args,o));
        }
        m
    }
    pub fn ops_vec(&self) -> Vec<(String, Vec<String>, Op)> {
        self.ops.clone()
    }
    pub fn add_sort<S: ToString>(&mut self, s: S) {
        self.sorts.insert(s.to_string(), 0);
    }
    pub fn add_type_con<S: ToString>(&mut self, s: S, arity: usize) {
        self.sorts.insert(s.to_string(), arity);
    }
    pub fn add_alias<S1: ToString>(&mut self, s: S1, t: VType) {
        let s = s.to_string();
        assert!(
            !t.contains_ui(&s),
            "Recursive type alias \"{}\" is not allowed",
            s,
        );
        assert!(t.validate(self, &Vec::new()) == Ok(()));
        self.type_aliases.insert(s, t);
    }
    pub fn add_constant<S1: ToString, S2: ToString>(
        &mut self,
        name: S1,
        sort: S2,
    ) {
        assert!(self.sorts.contains_key(&sort.to_string()));
        self.ops.push((
            name.to_string(),
            Vec::new(),
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
                self.sorts.contains_key(&i.to_string())
                    || self.type_aliases.get(&i.to_string()).is_some(),
                "{} is not a declared sort",
                i.to_string(),
            );
        }
        let op = Op::Symbol(PredSymbol{
            inputs: inputs
                .into_iter()
                .map(|s| VType::ui(s).expand_aliases(&self.type_aliases))
                .collect(),
        });
        self.ops.push((name.to_string(), Vec::new(), op));
    }
    pub fn add_relation_t<S1: ToString, const N: usize>(
        &mut self,
        name: S1,
        inputs: [VType; N],
    ) {
        for i in inputs.iter() {
            assert!(i.validate(self, &Vec::new()) == Ok(()));
        }
        let op = Op::Symbol(PredSymbol{
            inputs: inputs
                .into_iter()
                .map(|t| t.expand_aliases(&self.type_aliases))
                .collect(),
        });
        self.ops.push((name.to_string(), Vec::new(), op));
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
