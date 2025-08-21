use syn::{
    BinOp,
    Expr,
    ExprBinary,
    ExprBlock,
    ExprCall,
    ExprClosure,
    ExprIf,
    ExprLit,
    ExprMacro,
    ExprParen,
    ExprPath,
    ExprUnary,
    Lit,
    LitBool,
    Pat,
    PatIdent,
    Macro,
    ReturnType,
    Stmt,
    Type,
    UnOp,
};
use crate::{
    Builder,
    LogOpN,
    Sort,
    Pattern,
    Quantifier,
    Val,
    VName,
    VType,
};

type Error = String;

fn mk_err<A,T: ToString>(s: T) -> Result<A,Error> {
    Err(s.to_string())
}

// fn pat_ident(p: Pat) -> (Ident, Option<Ident>) {
//     match p {
//         Pat::Ident(PatIdent{ ident, .. }) => (ident, None),
//         Pat::Type(PatType{ pat, ty, .. }) => {
//             let ident = match *pat {
//                 Pat::Ident(PatIdent{ ident, .. }) => ident,
//                 p => panic!("Expected Pat::Ident, not {:?}", p),
//             };
//             let t = match *ty {
//                 Type::Path(p) => {
//                     p.path.get_ident().expect("Failed to get type").clone()
//                 }
//                 p => panic!("Expected Type::Path, not {:?}", p),
//             };
//             (ident, Some(t))
//         }
//         p => panic!("no ident extraction for {:?}", p),
//     }
// }

fn block_to_builder(stmt: Stmt, mut rem: Vec<Stmt>) -> Result<Builder,Error> {
    match stmt {
        Stmt::Local(l) => {
            let x = pat_to_vname(l.pat)?.0;
            let body = match l.init {
                Some(local_init) => *local_init.expr,
                None => return mk_err("let-bindings must have inits"),
            };
            let m = syn_to_builder(body)?;

            match rem.pop() {
                Some(next) => {
                    let n = block_to_builder(next,rem)?;
                    Ok(m.seq_pat(n)(x))
                }
                None => mk_err("terminating let-binding in block"),
            }
        }
        Stmt::Expr(expr,_) => {
            if rem.len() != 0 {
                mk_err(format!(
                    "non-terminating expr in block, remaining: {:?}",
                    rem.len(),
                ))
            } else {
                syn_to_builder(expr)
            }
        }
        s => todo!("block stmt {:?}", s),
    }
}

impl From<PatIdent> for VName {
    fn from(p: PatIdent) -> Self {
        VName::new(p.ident)
    }
}

impl VType {
    pub fn from_syn(t: Type) -> Result<Self, Error> {
        match t {
            Type::BareFn(t) => {
                let mut input_types = Vec::new();
                for arg in t.inputs.into_iter() {
                    input_types.push(VType::from_syn(arg.ty)?);
                }
                let output_type = match t.output {
                    ReturnType::Default => VType::unit(),
                    ReturnType::Type(_,t) => VType::from_syn(*t)?,
                };
                Ok(VType::fun_v(input_types, output_type))
            }
            Type::Path(p) => {
                match p.path.get_ident() {
                    Some(ty_i) => {
                        if ty_i == "bool" {
                            Ok(VType::prop())
                        } else {
                            Ok(VType::Atom(Sort::ui(ty_i)))
                        }
                    }
                    None => Err(format!("Can't handle type path {:?}", p)),
                }
            }
            Type::Tuple(p) => {
                let mut ts = Vec::new();
                for t in p.elems.into_iter() {
                    ts.push(Self::from_syn(t)?);
                }
                Ok(VType::Tuple(ts))
            }
            t => Err(format!("Can't handle type {:?}", t)),
        }
    }
}

fn pat_to_vname(p: Pat) -> Result<(Pattern, Option<VType>), Error> {
    match p {
        Pat::Ident(p) => Ok((Pattern::Atom(p.into()), None)),
        Pat::Tuple(p) => {
            let mut ps = Vec::new();
            for sub_p in p.elems.into_iter() {
                ps.push(pat_to_vname(sub_p)?.0);
            }
            Ok((Pattern::Tuple(ps), None))
        }
        Pat::Type(p) => {
            let (x,_) = pat_to_vname(*p.pat)?;
            let t = VType::from_syn(*p.ty)?;
            Ok((x,Some(t)))
        }
        Pat::Wild(..) => {
            Ok((Pattern::NoBind, None))
        }
        p => Err(format!("Can't handle binding Pat {:?}", p)),
    }
}

fn q_body(quantifier: Quantifier, expr: Expr) -> Result<Builder, Error> {
    match expr {
        Expr::Closure(ExprClosure{inputs,body,..}) => {
            assert!(
                inputs.len() >= 1,
                "Quantifiers must bind at least one variable"
            );
            let mut q_sig = Vec::new();
            for i in inputs.into_iter() {
                match pat_to_vname(i)? {
                    (x,Some(t)) => {
                        let x = match x.clone().unwrap_atom() {
                            Some(x) => x,
                            None => return Err(format!(
                                "Must not use tuple pattern in quantifier signature: {:?}",
                                x,
                            )),
                        };
                        q_sig.push((x, t)); }
                    (x,None) => {
                        return Err(format!(
                            "Quantified {:?} needs type annotation.",
                            x,
                        ))
                    }
                }
            }
            Ok(syn_to_builder(*body)?.quant(quantifier, q_sig))
        }
        e => {
            Err(format!(
                "Quantifier contained non-closure: {:?}",
                e,
            ))
        }
    }
}

pub fn syn_to_builder(e: Expr) -> Result<Builder, Error> {
    match e {
        Expr::Binary(ExprBinary{ left, op, right, .. }) => {
            let c1 = syn_to_builder(*left)?;
            let c2 = syn_to_builder(*right)?;
            Ok(match op {
                BinOp::And(_) => Builder::log_op(LogOpN::And, [c1,c2]),
                BinOp::Or(_) => Builder::log_op(LogOpN::Or, [c1,c2]),
                BinOp::Eq(_) => c1.eq_ne(true, c2),
                BinOp::Ne(_) => c1.eq_ne(false, c2),
                op => return mk_err(format!("Unhandled op: {:?}", op)),
            })
        }
        Expr::Block(ExprBlock{ block, .. }) => {
            let mut stmts = block.stmts;
            stmts.reverse();
            match stmts.pop() {
                Some(s) => block_to_builder(s, stmts),
                None => mk_err("Empty block"),
            }
        }
        Expr::If(ExprIf{ cond, mut then_branch, else_branch, .. }) => {
            let cond = syn_to_builder(*cond)?;
            let then_branch = match then_branch.stmts.pop() {
                Some(s) => block_to_builder(s, then_branch.stmts)?,
                None => Builder::return_(Val::unit()),
            };
            let else_branch = match else_branch {
                Some((_,b)) => syn_to_builder(*b)?,
                None => Builder::return_(Val::unit()),
            };
            Ok(cond.ite(then_branch, else_branch))
        }
        Expr::Lit(ExprLit{ lit, .. }) => match lit {
            Lit::Bool(LitBool{ value, .. }) => {
                if value {
                    Ok(Builder::return_(Val::true_()))
                } else {
                    Ok(Builder::return_(Val::false_()))
                }
            }
            lit => mk_err(format!("Unhandled lit: {:?}", lit)),
        }
        Expr::Call(ExprCall{ func, mut args, .. }) => {
            match *func {
                Expr::Path(p) if p.path.segments.len() == 1 && p.path.segments.first().unwrap().ident.to_string().as_str() == "forall" => {
                    assert!(
                        args.len() == 1,
                        "forall must take single closure as its only argument, got {:?}",
                        args,
                    );
                    q_body(Quantifier::Forall, args.pop().unwrap().into_value())
                }
                Expr::Path(p) if p.path.segments.len() == 1 && p.path.segments.first().unwrap().ident.to_string().as_str() == "exists" => {
                    assert!(
                        args.len() == 1,
                        "exists must take single closure as its only argument, got {:?}",
                        args,
                    );
                    q_body(Quantifier::Exists, args.pop().unwrap().into_value())
                }
                func => {
                    let f = syn_to_builder(func)?;
                    let mut cs = Vec::new();
                    for arg in args {
                        cs.push(syn_to_builder(arg)?);
                    }
        
                    // Note: this orders the Seq, Apply, and Force nodes
                    // differently than the previous algorithm, and
                    // differently to the CPBV algorithm. But it seems to be
                    // equivalent.
                    Ok(f.flatten().apply(cs))
                }
            }
        }

        Expr::Closure(ExprClosure{ inputs, body, .. }) => {
            let mut xs = Vec::new();
            for i in inputs.into_iter() {
                let (p,t) = pat_to_vname(i)?;
                let x = match p.clone().unwrap_atom() {
                    Some(x) => x,
                    None => return Err(format!(
                        "Must not use tuple pattern in function signature: {:?}",
                        p,
                    )),
                };
                xs.push((x,t));
            }
            Ok(Builder::return_thunk(
                syn_to_builder(*body)?.fun(xs)
            ))
        }

        Expr::Macro(ExprMacro{ mac: Macro{ path, tokens, .. }, .. }) => {
            // match 'path' into the quantifier
            let quantifier = match path.segments.first() {
                Some(s) => match s.ident.to_string().as_str() {
                    "forall" => Quantifier::Forall,
                    "exists" => Quantifier::Exists,
                    s => return Err(format!(
                        "Can't handle call to unknown macro '{}', expected only 'forall' or 'exists' in this context",
                        s,
                    )),
                }
                None => return Err(format!(
                    "Can't handle call to unknown macro '{:?}', expected only 'forall' or 'exists' in this context",
                    path,
                )),
            };

            // parse the tokens, then match result as a closure
            let expr: Expr = syn::parse(tokens.into()).unwrap();
            q_body(quantifier, expr)
        }

        Expr::Paren(ExprParen{expr,..}) => syn_to_builder(*expr),
        Expr::Path(ExprPath{path,..}) => match path.get_ident() {
            Some(i) => Ok(Builder::return_(VName::new(i).val())),
            None => Err(format!("Unhandled path: {:?}", path)),
        }
        Expr::Tuple(t) => {
            let mut bs = Vec::new();
            for e in t.elems.into_iter() {
                bs.push(syn_to_builder(e)?);
            }
            Ok(Builder::tuple(bs))
        }
        Expr::Unary(ExprUnary{op,expr,..}) => {
            let b = syn_to_builder(*expr)?;
            match op {
                UnOp::Not(_) => Ok(b.not()),
                op => Err(format!("Unhandled unary op {:?}", op)),
            }
        }

        e => mk_err(format!("Unhandled expr: {:?}", e)),
    }
}
