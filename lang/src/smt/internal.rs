use easy_smt;
use easy_smt::{Response, SExpr};
use crate::{
    Binder1,
    BType,
    FunOp,
    LogOpN,
    Comp,
    Gen,
    Literal,
    Oc,
    Op,
    OpCode,
    OpMode,
    Quantifier,
    Sig,
    Val,
    VName,
    VType,
    constructions,
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
        match &self.path {
            Some(p) => {
                let mut s = p.to_string();
                s.push_str(&mut "__".to_string());
                s.push_str(&mut self.ident.to_string());
                render_smt_op_name(s.as_str(), &self.types)
            }
            None => render_smt_op_name(&self.ident, &self.types),
        }
    }
}

fn declare_uf_fun_op(ctx: &mut easy_smt::Context, sig: &Sig, code: OpCode, p: FunOp) -> std::io::Result<()> {
    declare_uf(ctx, sig, code, p.inputs.clone(), p.output.clone())
}

fn declare_uf(ctx: &mut easy_smt::Context, sig: &Sig, code: OpCode, f_inputs: Vec<VType>, f_output: VType) -> std::io::Result<()> {
    println!("###\n### Declaring op {:?} to smt solver...\n###\n", code);
    let op_smt = code.render_smt();
    if f_inputs.len() == 0 {
        let sort = ctx.atom(format!(
            "{}",
            f_output
                .clone()
                .unwrap_base()
                .expect("declared zero-arg functions must have base output type")
                .render_smt(),
        ));
        println!("Declared {} as constant (zero-arg conversion) {}", code, op_smt);
        ctx.declare_const(op_smt, sort)?;
    } else {

        // For now, if there are any higher-order arguments,
        // we omit the functionality axiom.
        if !f_inputs.iter().any(|i| i.contains_thunk()) {
            let input_types: Vec<VType> =
                VType::flatten_many(f_inputs.clone());
            let output_types: Vec<VType> =
                VType::flatten(f_output.clone());
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

            let mut igen = Gen::new();

            // Include a functionality axiom for any op that has a
            // relational abstraction.
            let fun_axiom = constructions::fun_axiom(
                code.clone(),
                f_inputs,
                f_output,
            )
                .build(&mut igen)
                .normal_form_single_case(&sig, &mut igen);
    
            let mut builder = Context::new(ctx);
            let e = builder.smt(&fun_axiom)?;
            println!("SMT Axiom [Rel-Fun for {}]: {}", code, ctx.display(e[0]));
            ctx.assert(e[0])?;
        }
    }
    Ok(())
}

fn declare_con_exclusions(
    ctx: &mut easy_smt::Context,
    sig: &Sig,
    enum_type: VType,
    cons: Vec<(OpCode, Vec<VType>)>,
) -> std::io::Result<()> {
    // Declare same-constructor exclusion axioms.
    for (code,inputs) in cons.clone() {
        let mut igen = Gen::new();
        let axiom = constructions::same_con_exclusion_axiom(
            code.clone(),
            inputs,
            enum_type.clone(),
        )
            .build(&mut igen)
            .normal_form_single_case(&sig, &mut igen);
        let mut builder = Context::new(ctx);
        println!("SMT Axiom [Rel-Con-Same for {}]...", code);
        let e = builder.smt(&axiom)?;
        println!("SMT Axiom [Rel-Con-Same for {}]: {}", code, ctx.display(e[0]));
        ctx.assert(e[0])?;
    }

    // Collect every two differing constructors into a pair. When we
    // have pair (A,B), we don't also have pair (B,A).
    let con_pairs = crate::utility::unordered_cross(cons);
    // Declare different-constructor exclusion axioms.
    for ((code1,inputs1), (code2, inputs2)) in con_pairs {
        let mut igen = Gen::new();
        let axiom = constructions::diff_con_exclusion_axiom(
            code1.clone(),
            inputs1,
            code2.clone(),
            inputs2,
            enum_type.clone(),
        )
            .build(&mut igen)
            .normal_form_single_case(&sig, &mut igen);
        let mut builder = Context::new(ctx);
        println!(
            "SMT Axiom [Rel-Con-Diff for {} vs. {}]...",
            code1, code2,
        );
        let e = builder.smt(&axiom)?;
        println!(
            "SMT Axiom [Rel-Con-Diff for {} vs. {}]: {}",
            code1, code2,
            ctx.display(e[0])
        );
        ctx.assert(e[0])?;
    }
    Ok(())
}

fn declare_sig(ctx: &mut easy_smt::Context, sig: &Sig, term: &Comp) -> std::io::Result<()> {
    let (relevant, inst_axioms) = sig.relevant_with_axioms(term);

    for t in relevant.base_types() {
        if *t != BType::prop() {
            ctx.declare_sort(format!("{}", t.render_smt()), 0)?;
            println!("Declared {} as {}", t, t.render_smt());
        } else {
            println!("Ignoring relevant type Bool");
        }
    }

    // AFTER declaring all types, declare the contsructors for all relevant enum types
    for t in relevant.base_types() {
        match t {
            BType::UI(name, ts) => match sig.get_con_codes_with_inputs(name, ts.clone()) {
                Some(cs) => {
                    let output_type = VType::Base(t.clone());
                    for (code,inputs) in cs.clone() {
                        declare_uf(
                            ctx,
                            sig,
                            code,
                            inputs,
                            output_type.clone(),
                        )?;
                    }
                    declare_con_exclusions(ctx, sig, output_type, cs)?;
                }
                _ => {}
            }
            _ => {}
        }
    }

    for code in relevant.ops() {
        let op_smt = code.render_smt();
        match sig.get_applied_op_or_con(code).expect("relevant op should be defined") {
            // Enum constructors are all declared at the type level
            Oc::Con(..) => {},
            Oc::Op(Op::Const(p)) => {
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
            Oc::Op(Op::Symbol(p)) => {
                let input_atoms: Vec<_> = VType::flatten_many(p.inputs.clone())
                    .iter()
                    .map(|sort| {
                        let s = sort
                            .clone()
                            .unwrap_base()
                            .expect("symbol input types must be base");
                        ctx.atom(format!("{}", s.render_smt()))
                    })
                    .collect();
                println!("Declared {} as relation {} with {} inputs", code, op_smt, input_atoms.len());
                ctx.declare_fun(op_smt,input_atoms,ctx.atom("Bool"))?;
            }
            Oc::Op(Op::Fun(p)) => {
                declare_uf_fun_op(ctx, sig, code.clone(), p)?;
            }
            Oc::Op(Op::Rec(p)) => {
                declare_uf_fun_op(ctx, sig, code.clone(), p.as_fun_op())?;
            }
            Oc::Op(Op::Pred(..)) => {
                panic!("Can't hanlde Pred ops");
            }
            Oc::Op(op) => todo!("declare_sig for op {:?}", op),
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
        // println!("Defining {:?}", v);
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
        // println!("Cutting {}...", n);
        for _ in 0..n {
            self.cut()
        }
    }

    fn cut(&mut self) {
        let _a = self.assign.pop();
        // println!("Cut {:?}", a);
    }

    pub fn smt(&mut self, term: &Comp) -> std::io::Result<Vec<SExpr>> {
        println!("\n\nCalled smt on {:?}\n\n", term);
        self.smt_comp(term)
    }

    fn smt_val(&self, term: &Val) -> std::io::Result<SExpr> {
        match term {
            // Normalized Vars do not have type args, unless they are
            // constants.
            Val::Var(n, types, path, is_pos) => match self.get_assign(n) {
                Some(Assignment::Defined(e)) => {
                    assert!(is_pos, "Vars should only be negative when they are quantified, but {:?} is defined as {:?}", n, e);
                    Ok(e.clone())
                }
                Some(Assignment::Quantified) => {
                    let base = self.ctx.atom(n.as_string());
                    if *is_pos {
                        Ok(base)
                    } else {
                        Ok(self.ctx.not(base))
                    }
                }
                // Type-checking should have caught actual unbound
                // variables.  This must be a constant.
                None => {
                    match &n {
                        VName::Auto(_) =>
                            panic!("Ident {:?} seems to be unbound: {:?}", &n, &self.assign),
                        _ => {}
                    }
                    let code = OpCode {
                        ident: n.clone().unwrap_manual(),
                        types: types.clone(),
                        path: path.clone(),
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
                if q_sig.len() == 0 {
                    Ok(body[0])
                } else {
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
            }
            Binder1::LogOpN(op, vs) => {
                let mut args: Vec<SExpr> = Vec::new();
                for v in vs {
                    args.push(self.smt_val(v)?);
                }
                match op {
                    LogOpN::And if args.len() == 0 => Ok(self.ctx.true_()),
                    LogOpN::And => Ok(self.ctx.and_many(args)),
                    LogOpN::Or if args.len() == 0 => Ok(self.ctx.false_()),
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
