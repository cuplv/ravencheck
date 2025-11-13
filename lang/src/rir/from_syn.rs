//! Translation from Rust syntax (represented using the `syn` package)
//! into the Raven IR (RIR).

use syn::{
    AngleBracketedGenericArguments,
    BinOp,
    Block,
    Expr,
    ExprBinary,
    ExprBlock,
    ExprCall,
    ExprClosure,
    ExprIf,
    ExprLit,
    ExprMacro,
    ExprMethodCall,
    ExprParen,
    ExprUnary,
    FnArg,
    Ident as SynIdent,
    ItemFn,
    GenericArgument,
    GenericParam,
    Lit,
    LitBool,
    ParenthesizedGenericArguments,
    Pat,
    PatIdent,
    PatType,
    PathArguments,
    PathSegment,
    Macro,
    ReturnType,
    Signature,
    Stmt,
    Token,
    Type,
    TypeImplTrait,
    TypeParamBound,
    UnOp,
};
use syn::parse::{Parse, ParseStream};

use crate::{
    Builder,
    BType,
    Comp,
    InstRule,
    IGen,
    HypotheticalCall,
    LogOpN,
    MatchArm,
    OpCode,
    Pattern,
    Quantifier,
    Val,
    Ident as RirIdent,
    VType,
};

type Error = String;

fn mk_err<A,T: ToString>(s: T) -> Result<A,Error> {
    Err(s.to_string())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HypotheticalCallSyntax {
    pub call: ExprCall,
    pub arrow: Token![=>],
    pub output: SynIdent,
}

impl Parse for HypotheticalCallSyntax {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            call: input.parse()?,
            arrow: input.parse()?,
            output: input.parse()?,
        })
    }
}

impl HypotheticalCallSyntax {
    pub fn into_rir(self) -> Result<HypotheticalCall, Error> {
        let HypotheticalCallSyntax {call, output, ..} = self;
        let ExprCall{func, args, ..} = call;
        match *func {
            Expr::Path(p) => {
                assert!(p.path.segments.len() == 1);
                let PathSegment{ident, arguments} =
                    p.path.segments.first().unwrap().clone();
                let types = match arguments {
                    PathArguments::None => Vec::new(),
                    PathArguments::AngleBracketed(a) => {
                        a.args.into_pairs().map(|pr| {
                            match pr.into_value() {
                                GenericArgument::Type(t) =>
                                    VType::from_syn(t).unwrap(),
                                a => panic!("Can't handle this generic argument: {:?}", a),
                            }
                        }).collect()
                    }
                    PathArguments::Parenthesized(args) => {
                        panic!("Can't handle parenthesized path arguments: {:?}", args)
                    }
                };
                let types: Vec<String> = types
                    .into_iter()
                    .map(|t| match t.unwrap_base() {
                        Ok(BType::UI(s, ts)) if ts.len() == 0 => Ok(s),
                        Ok(b) => Err(format!("type args in #[assume(..)] or #[assert(..)] must be simple identifiers, instead got {}", b)),
                        Err(t) => Err(format!("type args in #[assume(..)] or #[assert(..)] must be simple identifiers, instead got {}", t.render())),
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let ident = ident.to_string();
                let inputs = args
                    .iter()
                    .map(|i| match i {
                        Expr::Path(p) => {
                            p.path.segments
                                .first()
                                .unwrap()
                                .clone()
                                .ident.to_string()
                        }
                        _ => panic!("Inputs must be simple identifiers"),
                    })
                    .collect();
                let output = output.to_string();
                Ok(HypotheticalCall{ident, tas: types, inputs, output})
            }
            _ => Err(format!("In #[assume_for(..)], called function must be by name, not an arbitrary expression.")),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstRuleSyntax {
    pub left: Type,
    pub arrow: Token![=>],
    pub right: AngleBracketedGenericArguments,
}

impl Parse for InstRuleSyntax {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            left: input.parse()?,
            arrow: input.parse()?,
            right: input.parse()?,
        })
    }
}

impl InstRule {
    pub fn from_syn(
        InstRuleSyntax{left,right,..}: InstRuleSyntax
    ) -> Result<Self, Error> {
        let left = match VType::from_syn(left)?.unwrap_base() {
            Ok(bt) => Ok(bt),
            Err(vt) => Err(format!("inst rule left-side should be a base type, but it was '{}'", vt.render())),
        }?;
        let right: Vec<VType> = right
            .args
            .into_pairs()
            .map(|p| p.into_value())
            .map(|ga| match ga {
                GenericArgument::Type(t) => t,
                ga => panic!("Can't handle type argument of form {:?}", ga),
            })
            .map(|t| VType::from_syn(t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(InstRule{left, right})
    }
}

pub fn block_to_builder(block: Block) -> Result<Builder, Error> {
    let mut stmts = block.stmts;
    stmts.reverse();
    match stmts.pop() {
        Some(s) => stmts_to_builder(s, stmts),
        None => mk_err("Empty block"),
    }
}

fn stmts_to_builder(stmt: Stmt, mut rem: Vec<Stmt>) -> Result<Builder,Error> {
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
                    let n = stmts_to_builder(next,rem)?;
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

impl From<PatIdent> for RirIdent {
    fn from(p: PatIdent) -> Self {
        RirIdent::new(p.ident)
    }
}

impl BType {
    pub fn from_string<S: ToString>(s: S) -> Result<Self, Error> {
        let vt = VType::from_string(s)?;
        match vt.unwrap_base() {
            Ok(bt) => Ok(bt),
            Err(vt) => Err(format!("{} is not a base type", vt.render())),
        }
    }
}

fn get_fn_from_impl(mut t: TypeImplTrait) -> Option<(Vec<VType>, VType)> {
    if t.bounds.len() != 1 {
        return None;
    }
    match t.bounds.pop().unwrap().into_value() {
        TypeParamBound::Trait(mut t) => {
            if t.path.segments.len() != 1 {
                return None;
            }
            let seg = t.path.segments.pop().unwrap().into_value();
            match seg.ident.to_string().as_str() {
                "Fn" | "FnMut" | "FnOnce" => match seg.arguments {
                    PathArguments::Parenthesized(ParenthesizedGenericArguments{inputs, output: ReturnType::Type(_, output), ..}) => {
                        let inputs = inputs
                            .into_pairs()
                            .map(|i| VType::from_syn(i.into_value()).unwrap())
                            .collect();
                        match VType::from_syn(*output) {
                            Ok(output) => Some((inputs, output)),
                            Err(_) => None,
                        }

                    }
                    _ => None
                }
                _ => None
            }
        }
        _ => None
    }

}

impl VType {
    pub fn from_pat_type<S: ToString>(s: S) -> Result<Self, Error> {
        let pt: PatType = match syn::parse_str(&s.to_string()) {
            Ok(t) => t,
            Err(e) => panic!(
                "Could not parse \"{}\" as a typed pattern: {}",
                s.to_string(),
                e,
            ),
        };
        Self::from_syn(*pt.ty)
    }
    pub fn from_string<S: ToString>(s: S) -> Result<Self, Error> {
        let t: Type = match syn::parse_str(&s.to_string()) {
            Ok(t) => t,
            Err(e) => panic!(
                "Could not parse \"{}\" as a type: {}",
                s.to_string(),
                e,
            ),
        };
        Self::from_syn(t)
    }
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
            Type::ImplTrait(t) => {
                match get_fn_from_impl(t.clone()) {
                    Some((inputs, output)) =>
                        Ok(VType::fun_v(inputs, output)),
                    None => panic!(
                        "impl should be a closure trait with output: {:?}",
                        t,
                    ),
                }
            }
            Type::Path(mut p) => {
                if p.path.segments.len() == 1 {
                    let seg = p.path.segments.pop().unwrap().into_value();
                    if &seg.ident == "bool" {
                        Ok(VType::prop())
                    } else {
                        let mut args = match seg.arguments {
                            PathArguments::None => Vec::new(),
                            PathArguments::AngleBracketed(bs) => {
                                bs
                                    .args
                                    .into_pairs()
                                    .map(|p| p.into_value())
                                    .map(|ga| match ga {
                                        GenericArgument::Type(t) => t,
                                        ga => panic!("Can't handle type argument of form {:?}", ga),
                                    })
                                    .map(|t| VType::from_syn(t).unwrap())
                                    .collect()
                            }
                            PathArguments::Parenthesized(..) => return Err(format!("Can't handle parenthesized type arguments")),
                        };
                        if &seg.ident == "Box" {
                            assert!(args.len() == 1, "Box<_> should have 1 type arg, but it was given {} type args", args.len());
                            Ok(args.pop().unwrap())
                        } else {
                            Ok(VType::Base(BType::UI(seg.ident.to_string(), args)))
                        }
                    }
                } else {
                    Err(format!("Can't handle type path {:?}, since it does not have exactly 1 segment.", p))
                }
            }
            Type::Reference(t) => Self::from_syn(*t.elem),
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

impl Pattern {
    pub fn from_pat(p: Pat) -> Result<(Self, Option<VType>), Error> {
        pat_to_vname(p)
    }
    pub fn from_pat_type(pt: PatType) -> Result<(Self, VType), Error> {
        let (p,t) = pat_to_vname(Pat::Type(pt))?;
        Ok((p, t.unwrap()))
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

fn get_cloned_expr(e: ExprMethodCall) -> Result<Expr, Error> {
    match e.method.to_string().as_str() {
        "clone" => Ok(*e.receiver),
        m => Err(format!("only 'clone' should be used as a method call, found '{}'", m)),
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
                Some(s) => stmts_to_builder(s, stmts),
                None => mk_err("Empty block"),
            }
        }
        Expr::If(ExprIf{ cond, mut then_branch, else_branch, .. }) => {
            let cond = syn_to_builder(*cond)?;
            then_branch.stmts.reverse();
            let then_branch = match then_branch.stmts.pop() {
                Some(s) => stmts_to_builder(s, then_branch.stmts)?,
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
        Expr::MethodCall(e) => syn_to_builder(get_cloned_expr(e)?),
        Expr::Call(ExprCall{ func, mut args, .. }) => {
            let func = *func;
            if is_box_new(&func) {
                if args.len() == 1 {
                    syn_to_builder(args.pop().unwrap().into_value())
                } else {
                    Err(format!(
                        "Box::new(..) should take one argument but it has {}",
                        args.len(),
                    ))
                }
            } else {
                match func {
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
            let xs = xs
                .into_iter()
                .map(|(x,o)| match o {
                    Some(t) => Ok((x,t)),
                    None => Err(format!(
                        "Closure arguments must have type annotations."
                    )),
                })
                .collect::<Result<Vec<_>,_>>()?;
            Ok(Builder::return_thunk(
                syn_to_builder(*body)?.into_fun(xs)
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

        Expr::Match(expr) => {
            let target = syn_to_builder(*expr.expr)?;
            let arms: Vec<(MatchArm, Builder)> = expr.arms
                .into_iter()
                .map(|arm| {
                    match arm.pat {
                        Pat::TupleStruct(pat) => {
                            assert!(
                                pat.path.segments.len() == 2,
                                "match arm path should have 2 segments",
                            );
                            let segments: Vec<&PathSegment> =
                                pat.path.segments.iter().collect();
                            let ty_seg = segments[0].clone();
                            let ty: String =
                                ty_seg.ident.to_string();
                            let targs: Vec<VType> = type_args_from_seg(ty_seg)?;
                            let constructor: String =
                                segments[1].clone().ident.to_string();
                            let code = OpCode {
                                ident: constructor,
                                path: Some(ty),
                                types: targs,
                            };

                            let binders: Vec<Pattern> = pat.elems
                                .iter()
                                .map(|p| {
                                    Pattern::from_pat(p.clone()).map(|tup|tup.0)
                                })
                                .collect::<Result<Vec<_>, _>>()?;

                            let comp = syn_to_builder(*arm.body)?;
                            Ok((MatchArm{code, binders}, comp))
                        }
                        Pat::Path(pat) => {
                            assert!(
                                pat.path.segments.len() == 2,
                                "match arm path should have 2 segments",
                            );
                            let segments: Vec<&PathSegment> =
                                pat.path.segments.iter().collect();
                            let ty_seg = segments[0].clone();
                            let ty: String =
                                ty_seg.ident.to_string();
                            let targs: Vec<VType> = type_args_from_seg(ty_seg)?;
                            let constructor: String =
                                segments[1].clone().ident.to_string();
                            let code = OpCode {
                                ident: constructor,
                                path: Some(ty),
                                types: targs,
                            };

                            let comp = syn_to_builder(*arm.body)?;
                            Ok((MatchArm{
                                code,
                                binders: Vec::new()
                            }, comp))
                        }
                        p => panic!("can't parse match arm from {:?}", p),
                    }
                })
                .collect::<Result<Vec<_>, Error>>()?;
            Ok(target.mat(arms))
        }

        Expr::Paren(ExprParen{expr,..}) => syn_to_builder(*expr),

        Expr::Path(mut ep) => {
            if ep.path.segments.len() == 1 {
                let PathSegment{ident,arguments} =
                    ep.path.segments.pop().unwrap().into_value();
                let types = match arguments {
                    PathArguments::None => Vec::new(),
                    PathArguments::AngleBracketed(a) => {
                        a.args.into_pairs().map(|pr| {
                            match pr.into_value() {
                                GenericArgument::Type(t) =>
                                    VType::from_syn(t).unwrap(),
                                a => panic!("Can't handle this generic argument: {:?}", a),
                            }
                        }).collect()
                    }
                    PathArguments::Parenthesized(args) => {
                        panic!("Can't handle parenthesized path arguments: {:?}", args)
                    }
                };
                // This could be either a primitive function call
                // (with type args) or a variable (which cannot have
                // type args). For now, we do not distinguish here.
                let code = OpCode::fun_types(ident, types);
                Ok(code.as_fun().builder())
            } else if ep.path.segments.len() == 2 {
                let PathSegment{ident: ident2, arguments: arguments2} =
                    ep.path.segments.pop().unwrap().into_value();
                let PathSegment{ident: ident1, arguments: arguments1} =
                    ep.path.segments.pop().unwrap().into_value();
                // Get the type arguments from the first path seg
                let types = match arguments1 {
                    PathArguments::None => Vec::new(),
                    PathArguments::AngleBracketed(a) => {
                        a.args.into_pairs().map(|pr| {
                            match pr.into_value() {
                                GenericArgument::Type(t) =>
                                    VType::from_syn(t).unwrap(),
                                a => panic!("Can't handle this generic argument: {:?}", a),
                            }
                        }).collect()
                    }
                    PathArguments::Parenthesized(args) => {
                        panic!("Can't handle parenthesized path arguments: {:?}", args)
                    }
                };
                assert!(
                    arguments2 == PathArguments::None,
                    "2-segment paths should not have type args on second seg: {:?}",
                    ep.path,
                );
                let code = OpCode::enum_con(ident1, types, ident2);
                Ok(code.as_fun().builder())
                // Ok(Builder::return_(Val::Var(RirIdent::new(ident2), types, Some(ident1.to_string()))))
            } else {
                panic!("Got path with more than 2 segments: {:?}", ep.path)
            }
        }

        Expr::Reference(e) => syn_to_builder(*e.expr),

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
                UnOp::Deref(_) => Ok(b),
                op => Err(format!("Unhandled unary op {:?}", op)),
            }
        }

        e => mk_err(format!("Unhandled expr: {:?}", e)),
    }
}

#[derive(Clone)]
pub struct RirFnSig {
    pub ident: String,
    pub tas: Vec<String>,
    pub inputs: Vec<(Pattern, VType)>,
    pub output: VType,
}

impl RirFnSig {
    pub fn from_syn(sig: Signature) -> Result<Self, Error> {
        let Signature{ident, generics, inputs, output, ..} = sig;
        let ident = ident.to_string();
        let tas = generics.params
            .into_pairs()
            .filter_map(|p| match p.into_value() {
                GenericParam::Type(tp) => Some(tp.ident.to_string()),
                _ => None,
            })
            .collect();
        let inputs = inputs
            .into_pairs()
            .map(|p| match p.into_value() {
                FnArg::Typed(pt) => Pattern::from_pat_type(pt),
                FnArg::Receiver(_) => Err(format!("function '{}' should not take a 'self' input", &ident)),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output = match output {
            ReturnType::Default => Err(format!("function '{}' has unspecified return type", &ident)),
            ReturnType::Type(_, t) => VType::from_syn(*t),
        }?;
        Ok(RirFnSig{ident, tas, inputs, output})
    }
    pub fn input_types(&self) -> Vec<VType> {
        self.inputs.iter().map(|(_,t)| t.clone()).collect()
    }
}

#[derive(Clone)]
pub struct RirFn {
    pub sig: RirFnSig,
    pub body: Comp,
}

impl RirFn {
    /// Return a `Builder` that uses the fn item's arguments
    /// as the signature of a universal quantifier.
    pub fn into_uni_formula(
        self
    ) -> Result<(String, Vec<String>, Builder), String> {
        let Self{sig, body} = self;
        // The output type is expected to be bool, but we don't
        // check/enforce that here.
        let RirFnSig{ident, tas, inputs, ..} = sig;
        // If there are arguments to quantify, then wrap the fn item's
        // body in a universal quantifier that quantifies them.
        //
        // Otherwise, just convert the unchanged body into a
        // `Builder`.
        let body = if inputs.len() > 0 {
            let inputs = inputs
                .into_iter()
                .map(|(p,t)| Ok((p.unwrap_vname()?, t)))
                .collect::<Result<Vec<_>,String>>()?;
            Builder::lift(body).quant(
                Quantifier::Forall,
                inputs,
            )
        } else {
            Builder::lift(body)
        };
        Ok((ident, tas, body))
    }

    pub fn from_syn(
        ItemFn{sig, block, ..}: ItemFn,
    ) -> Result<Self, Error> {
        let sig = RirFnSig::from_syn(sig)?;
        let body = match block_to_builder(*block) {
            Ok(b) => Ok(b.build_with(&mut IGen::new())),
            Err(e) => Err(e),
        }?;
        Ok(RirFn{sig, body})
    }
}

fn type_args_from_seg(seg: PathSegment) -> Result<Vec<VType>, String> {
    match seg.arguments {
        PathArguments::None => Ok(Vec::new()),
        PathArguments::AngleBracketed(bs) => {
            bs
                .args
                .into_pairs()
                .map(|p| p.into_value())
                .map(|ga| match ga {
                    GenericArgument::Type(t) =>
                        VType::from_syn(t),
                    ga => Err(format!("Can't handle type argument of form {:?}", ga)),
                })
                // .map(|t| VType::from_syn(t).unwrap())
                .collect::<Result<Vec<_>, _>>()
        }
        PathArguments::Parenthesized(..) => Err(format!("Can't handle parenthesized type arguments")),
    }
}

fn is_box_new(expr: &Expr) -> bool {
    match expr {
        Expr::Path(expr) => {
            let segs = &expr.path.segments;
            segs.len() == 2 && &segs[0].ident == "Box" && &segs[1].ident == "new"
        }
        _ => false,
    }
}
