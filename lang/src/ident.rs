/// Identifiers, which may be variable names or function names.
///
/// Variable names may be automatically generated.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ident {
    Manual(String),
    Auto(u32),
}

impl Ident {
    pub fn as_string(&self) -> String {
        match self {
            Self::Manual(s) => format!("x_{}", s),
            Self::Auto(n) => format!("xn_{}", n),
        }
    }
    pub fn as_symbol_string(&self) -> String {
        match self {
            Self::Manual(s) => format!("{}", s),
            x => panic!("Can't format {:?} as a symbol name", x),
        }
    }
    pub fn new<T: ToString>(s: T) -> Self {
        Self::Manual(s.to_string())
    }
    pub fn auto(n: u32) -> Self {
        Self::Auto(n)
    }
    pub fn unwrap_manual(self) -> String {
        match self {
            Self::Manual(s) => s,
            x => format!("Tried to unwrap manual Ident, got {:?}", x),
        }
    }
}
