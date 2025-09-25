use easy_smt;
use easy_smt::{Response, SExpr};
use crate::{
    Binder1,
    Builder,
    BType,
    FunOp,
    LogOpN,
    Comp,
    Gen,
    Literal,
    Op,
    OpCode,
    OpMode,
    Quantifier,
    Sig,
    Val,
    VName,
    VType,
};

impl BType {
    fn render_smt(&self) -> String {
        match self {
            BType::Prop => format!("Bool"),
            BType::UI(name, args) if args.len() == 0 => format!("UI_{}", name),
            BType::UI(name, args) => {
                let mut s = format!("UI_{}__", name);
                for a in args {
                    s.push_str(&a.render_smt());
                }
                s.push_str("__");
                s
            }
        }
    }
}

impl VType {
    fn render_smt(&self) -> String {
        match self {
            VType::Base(bt) => bt.render_smt(),
            VType::Thunk(..) => panic!("Cannot render_smt for Thunk type"),
            VType::Tuple(ts) => {
                let mut s = format!("TUPLE__");
                for t in ts {
                    s.push_str(&t.render_smt());
                }
                s.push_str("__");
                s
            }
        }
    }
}

fn render_smt_op_name(name: &str, ts: &Vec<VType>) -> String {
    let mut s = format!("F_{}__", name);
    for t in ts {
        s.push_str(&t.render_smt());
    }
    s.push_str("__");
    s
}

impl OpCode {
    fn render_smt(&self) -> String {
        render_smt_op_name(&self.ident, &self.types)
    }
}

fn declare_uf(ctx: &mut easy_smt::Context, sig: &Sig, code: OpCode, p: FunOp) -> std::io::Result<()> {
    let op_smt = code.render_smt();
    if p.inputs.len() == 0 {
        let sort = ctx.atom(format!(
            "{}",
            p.output
                .clone()
                .unwrap_base()
                .expect("declared zero-arg functions must have base output type")
                .render_smt(),
        ));
        println!("Declared {} as constant (zero-arg conversion) {}", code, op_smt);
        ctx.declare_const(op_smt, sort)?;
        // todo!("Declare zero-arg fun");
    } else {

        // For now, if there are any higher-order arguments,
        // we omit the functionality axiom.
        if !p.inputs.iter().any(|i| i.contains_thunk()) {
            let input_types: Vec<VType> =
                VType::flatten_many(p.inputs.clone());
            let output_types: Vec<VType> =
                VType::flatten(p.output.clone());
            let rel_type_atoms: Vec<SExpr> = input_types
                .iter()
                .chain(output_types.iter())
                .map(|sort| {
                    let s = sort
                        .clone()
                        .unwrap_base()
                        .expect("sig types must be atoms");
                    ctx.atom(format!("{}", s.render_smt()))
                })
                .collect();
            ctx.declare_fun(
                op_smt.clone(),
                rel_type_atoms,
                ctx.atom("Bool"),
            )?;
            println!("Declared {} as absrel {}", code, op_smt);
    
            let mut vgen = Gen::new();
            let ixs = vgen.next_many(input_types.len());
            let oxs1 = vgen.next_many(output_types.len());
            let oxs2 = vgen.next_many(output_types.len());
            let q_sig: Vec<(VName, VType)> = ixs
                .iter()
                .cloned()
                .zip(input_types.iter().cloned())
                .chain(
                    oxs1
                       .iter()
                       .cloned()
                       .zip(output_types.iter().cloned())
                )
                .chain(
                    oxs2
                       .iter()
                       .cloned()
                       .zip(output_types.iter().cloned())
                )
                .collect();
    
            let args1: Vec<Val> = ixs
                .iter()
                .cloned()
                .chain(oxs1.iter().cloned())
                .map(|i| i.val())
                .collect();
            let args2: Vec<Val> = ixs
                .iter()
                .cloned()
                .chain(oxs2.iter().cloned())
                .map(|i| i.val())
                .collect();
    
            let otup1: Builder = Builder::tuple(
                oxs1
                    .iter()
                    .cloned()
                    .map(|x| Builder::return_(x.val()))
                    .collect::<Vec<Builder>>()
            );
            let otup2: Builder = Builder::tuple(
                oxs2
                    .iter()
                    .cloned()
                    .map(|x| Builder::return_(x.val()))
                    .collect::<Vec<Builder>>()
            );
    
            let fun_axiom = Builder::log_op(
                LogOpN::Or,
                [
                    Builder::log_op(
                        LogOpN::And,
                        [
                            Builder::force(Val::OpCode(OpMode::RelAbs, code.clone()))
                                .apply_v(args1),
                            Builder::force(Val::OpCode(OpMode::RelAbs, code.clone()))
                                .apply_v(args2),
                        ]
                    )
                        .not(),
                    otup1.eq_ne(true, otup2),
                ]
            )
                .quant(Quantifier::Forall, q_sig)
                .build(&mut vgen)
                .normal_form_single_case(&sig, &mut vgen);
    
            let mut builder = Context::new(ctx);
            let e = builder.smt(&fun_axiom)?;
            println!("SMT Axiom [Rel]: {}", ctx.display(e[0]));
            ctx.assert(e[0])?;
        }
    }
    Ok(())
}

fn declare_sig(ctx: &mut easy_smt::Context, sig: &Sig, term: &Comp) -> std::io::Result<()> {
    let (relevant, inst_axioms) = sig.relevant_with_axioms(term);

    for t in relevant.base_types() {
        assert!(
            *t != BType::prop(),
            "Bool should not be listed as a relevant type"
        );
        ctx.declare_sort(format!("{}", t.render_smt()), 0)?;
        println!("Declared {} as {}", t, t.render_smt());
    }

    for code in relevant.ops() {
        let op_smt = code.render_smt();
        match sig.get_applied_op(code).expect("relevant op should be defined") {
            Op::Const(p) => {
                let sort = ctx.atom(format!(
                    "{}",
                    p.vtype
                        .clone()
                        .unwrap_base()
                        .expect("const types must be base")
                        .render_smt(),
                ));
                println!("Declared {} as constant {}", code, op_smt);
                ctx.declare_const(op_smt, sort)?;
            }
            Op::Symbol(p) => {
                let input_atoms = VType::flatten_many(p.inputs.clone())
                    .iter()
                    .map(|sort| {
                        let s = sort
                            .clone()
                            .unwrap_base()
                            .expect("symbol input types must be base");
                        ctx.atom(format!("{}", s.render_smt()))
                    })
                    .collect();
                println!("Declared {} as relation {}", code, op_smt);
                ctx.declare_fun(op_smt,input_atoms,ctx.atom("Bool"))?;
            }
            Op::Fun(p) => {
                declare_uf(ctx, sig, code.clone(), p)?;
            }
            Op::Rec(p) => {
                declare_uf(ctx, sig, code.clone(), p.as_fun_op())?;
            }
            Op::Pred(..) => {
                panic!("Can't hanlde Pred ops");
            }
            op => todo!("declare_sig for op {:?}", op),
        }
    }

    for a in &inst_axioms {
        let mut builder = Context::new(ctx);
        let e = builder.smt(a)?;
        println!("SMT Axiom: {}", ctx.display(e[0]));
        ctx.assert(e[0])?;
    }
    Ok(())
}

pub fn check_sat_of_normal(
    term: &Comp,
    sig: &Sig,
) -> std::io::Result<Response> {
    // See https://github.com/cvc5/cvc5/issues/6274
    // for explanation of 3rd and 4th options.
    //
    // Without them, cvc5 will often return Unknown rather than Sat or
    // Unsat.
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("cvc5", [
            "--lang", "smt2",
            "--full-saturate-quant",
            "--finite-model-find",
        ])
        .build()?;
    ctx.set_logic("ALL")?;
    declare_sig(&mut ctx, sig, term)?;
    // println!("Normal: {:?}", term_normal);
    let mut builder = Context::new(&mut ctx);
    let e = builder.smt(&term)?;
    println!("SMT: {}", ctx.display(e[0]));
    ctx.assert(e[0])?;
    return ctx.check()    
}

#[cfg(test)]
pub fn check_sat_simple(
    term: &Comp,
    sig: &Sig,
) -> std::io::Result<Response> {
    let cases = term.clone().normal_form(sig);

    for (name,comp) in cases.into_iter() {
        // See https://github.com/cvc5/cvc5/issues/6274
        // for explanation of 3rd and 4th options.
        //
        // Without them, cvc5 will often return Unknown rather than Sat or
        // Unsat.
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("cvc5", [
                "--lang", "smt2",
                "--full-saturate-quant",
                "--finite-model-find",
            ])
            .build()?;
        ctx.set_logic("ALL")?;
        declare_sig(&mut ctx, sig, &comp)?;

        let mut builder = Context::new(&mut ctx);
        let e = builder.smt(&comp)?;
        println!("SMT case [{}]: {}", name.to_string(), ctx.display(e[0]));
        ctx.assert(e[0])?;
        match ctx.check()? {
            Response::Unsat => {},
            Response::Sat => {
                println!("Got SAT for case [{}]", name.to_string());
                return Ok(Response::Sat);
            }
            Response::Unknown => {
                println!("Got UNKNOWN for case [{}]", name.to_string());
                return Ok(Response::Unknown);
            }
        }
    }
    // If we pass all cases, or if there were somehow no cases, the
    // result is valid/UNSAT.
    Ok(Response::Unsat)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Assignment {
    Quantified,
    Defined(SExpr),
}

struct Context<'a> {
    ctx: &'a mut easy_smt::Context,
    assign: Vec<(VName,Assignment)>,
}

impl <'a> Context<'a> {
    pub fn new<'b: 'a>(ctx: &'b mut easy_smt::Context) -> Self {
        Self {
            ctx,
            assign: Vec::new(),
        }
    }

    fn get_assign(&self, v: &VName) -> Option<Assignment> {
        for (v2,e) in self.assign.iter().rev() {
            if v2 == v {
                return Some(e.clone())
            }
        }
        None
    }

    fn define(&mut self, v: &VName, e: &SExpr) {
        self.assign.push((v.clone(), Assignment::Defined(e.clone())));
    }

    fn with_define<F,A>(&mut self, v: &VName, e: &SExpr, f: F) -> A
    where F: Fn(&mut Self) -> A {
        self.define(v,e);
        let a = f(self);
        self.cut();
        a
    }

    fn quantify(&mut self, v: &VName) {
        self.assign.push((v.clone(), Assignment::Quantified));
    }

    fn with_quantify<F,A,S>(&mut self, xs: &Vec<(VName,S)>, f: F) -> A
    where F: Fn(&mut Self) -> A {
        for (x,_) in xs {
            self.quantify(x);
        }
        let a = f(self);
        self.cut_n(xs.len());
        a
    }

    fn cut_n(&mut self, n: usize) {
        for _ in [0..n] {
            self.cut()
        }
    }

    fn cut(&mut self) {
        self.assign.pop();
    }

    pub fn smt(&mut self, term: &Comp) -> std::io::Result<Vec<SExpr>> {
        self.smt_comp(term)
    }

    fn smt_val(&self, term: &Val) -> std::io::Result<SExpr> {
        match term {
            // Normalized Vars do not have type args, unless they are constants
            Val::Var(n, types, _) => match self.get_assign(n) {
                Some(Assignment::Defined(e)) =>
                    Ok(e.clone()),
                Some(Assignment::Quantified) =>
                    Ok(self.ctx.atom(n.as_string())),
                // Type-checking should have caught actual unbound
                // variables.  This must be a constant.
                None => {
                    let code = OpCode {
                        ident: n.clone().unwrap_manual(),
                        types: types.clone(),
                        path: None,
                    };
                    Ok(self.ctx.atom(code.render_smt()))
                }
            }
            Val::Literal(Literal::LogTrue) =>
                Ok(self.ctx.true_()),
            Val::Literal(Literal::LogFalse) =>
                Ok(self.ctx.false_()),
            Val::OpCode(om,oc) => match om {
                OpMode::Const | OpMode::ZeroArgAsConst =>
                    Ok(self.ctx.atom(oc.render_smt())),
                OpMode::RelAbs =>
                    panic!("RelAbs({:?}) should not appear as a value after normalization", oc),
            }
            Val::Thunk(_) =>
                panic!("Thunks must be eliminated before smt"),
            Val::Tuple(_) =>
                panic!("Tuple values must be eliminated before smt: {:?}", term),
        }
    }

    fn smt_binder_1(&mut self, term: &Binder1) -> std::io::Result<SExpr> {
        match term {
            Binder1::Eq(pos, args1, args2) => {
                let mut props = Vec::new();
                for (a,b) in args1.iter().zip(args2) {
                    let a = self.smt_val(a)?;
                    let b = self.smt_val(b)?;
                    if *pos {
                        props.push(self.ctx.eq(a,b));
                    } else {
                        props.push(self.ctx.distinct(a,b));
                    }
                }
                if *pos {
                    Ok(self.ctx.and_many(props))
                } else {
                    Ok(self.ctx.or_many(props))
                }
            }
            Binder1::LogQuantifier(q,xs,m) => {
                let body = self.with_quantify(xs, |ctx| ctx.smt_comp(m))?;
                let q_sig = xs.iter().map(|(x,s)| {
                    let s = s.clone().unwrap_base()
                        .expect("quantifier types should be flattened to base types before smt");
                    (x.as_string(), self.ctx.atom(s.render_smt()))
                });
                match q {
                    Quantifier::Exists => {
                        Ok(self.ctx.exists(
                            q_sig,
                            body[0],
                        ))
                    }
                    Quantifier::Forall => {
                        Ok(self.ctx.forall(
                            q_sig,
                            body[0],
                        ))
                    }
                }
            }
            Binder1::LogOpN(op, vs) => {
                let mut args: Vec<SExpr> = Vec::new();
                for v in vs {
                    args.push(self.smt_val(v)?);
                }
                match op {
                    LogOpN::And => Ok(self.ctx.and_many(args)),
                    LogOpN::Or => Ok(self.ctx.or_many(args)),
                    // LogOpN::Pred(_oc,true) => todo!("smt Pred-true"),
                    LogOpN::Pred(oc,true) => {
                        args.insert(0, self.ctx.atom(oc.render_smt()));
                        Ok(self.ctx.list(args))
                    },
                    // LogOpN::Pred(_oc,false) => todo!("smt Pred-false"),
                    LogOpN::Pred(oc,false) => {
                        args.insert(0, self.ctx.atom(oc.render_smt()));
                        Ok(self.ctx.not(self.ctx.list(args)))
                    },
                }
            }
            t => panic!("No smt for Binder1 {:?}", t),
        }
    }

    fn smt_comp(&mut self, term: &Comp) -> std::io::Result<Vec<SExpr>> {
        match term {
            Comp::Apply(_m, _targs, _vs) =>
                panic!("Apply must be eliminated before smt generation"),
            Comp::BindN(_b,_vs,_m) => todo!(
                "Comp::BindN terms should be eliminated before smt generation: {:?}",
                term,
            ),
            Comp::Bind1(b,v,m) => {
                let bindee = self.smt_binder_1(&b)?;
                self.with_define(v, &bindee, |ctx| ctx.smt_comp(m))
            }
            Comp::Force(_v) =>
                panic!("Force must be eliminated before smt generation"),
            Comp::Fun(_,_) =>
                panic!("Fun must be eliminated before smt generation: {:?}", term),
            Comp::Ite(cond, then_branch, else_branch) => {
                let cond = self.smt_val(cond)?;
                let then_b = self.smt_comp(then_branch)?[0];
                let else_b = self.smt_comp(else_branch)?[0];
                Ok(vec![self.ctx.and(
                    self.ctx.or(
                        self.ctx.not(cond),
                        then_b,
                    ),
                    self.ctx.or(
                        cond,
                        else_b,
                    )
                )])
            }
            Comp::Return(vs) => {
                let mut args: Vec<SExpr> = Vec::new();
                for v in vs {
                    args.push(self.smt_val(v)?);
                }
                Ok(args)
            }
            c => todo!("smt_comp for {:?}", c),
        }
    }
}
