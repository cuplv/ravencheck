/// Variable names
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VName {
    Manual(String),
    Auto(u32),
}

impl VName {
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
    pub fn new<T: ToString>(s: T) -> VName {
        VName::Manual(s.to_string())
    }
    pub fn auto(n: u32) -> VName {
        VName::Auto(n)
    }
    pub fn unwrap_manual(self) -> String {
        match self {
            Self::Manual(s) => s,
            x => format!("Tried to unwrap manual VName, got {:?}", x),
        }
    }
}
