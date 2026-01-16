use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;

use syn::{
    Attribute,
    Error as SynError,
    FnArg,
    Ident,
    Item,
    ItemFn,
    ItemMod,
    ItemUse,
    LitStr,
    Meta,
    Pat,
    Path,
    PathArguments,
    PathSegment,
    punctuated::Punctuated,
    spanned::Spanned,
    Stmt,
    Token,
    UseTree,
    parse_quote,
};
use syn::ext::IdentExt;
use syn::parse::Parser;

use std::collections::VecDeque;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::fmt;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum SynItemTag {
    Const,
    Enum,
    Fn,
    Impl,
    Mod,
    Struct,
    Type,
    Use,
}

impl fmt::Display for SynItemTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Const => "const",
            Self::Enum => "enum",
            Self::Fn => "fn",
            Self::Impl => "impl",
            Self::Mod => "mod",
            Self::Struct => "struct",
            Self::Type => "type",
            Self::Use => "use",
        };
        write!(f, "{}", s)
    }
}

impl SynItemTag {
    fn tag_attrs(item: &mut Item) -> Option<(SynItemTag, &mut Vec<Attribute>)> {
        match item {
            Item::Const(i) => Some((Self::Const, &mut i.attrs)),
            Item::Enum(i) => Some((Self::Enum, &mut i.attrs)),
            Item::Fn(i) => Some((Self::Fn, &mut i.attrs)),
            Item::Impl(i) => Some((Self::Impl, &mut i.attrs)),
            Item::Mod(i) => Some((Self::Mod, &mut i.attrs)),
            Item::Struct(i) => Some((Self::Struct, &mut i.attrs)),
            Item::Type(i) => Some((Self::Type, &mut i.attrs)),
            Item::Use(i) => Some((Self::Use, &mut i.attrs)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RvnItemAttr {
    Annotate(String),
    AnnotateMulti,
    Assume,
    AssumeFor(String),
    Declare,
    Define,
    Falsify,
    // Should only be used with AnnotateMulti
    ForCall(String),
    // Should only be used with AnnotateMulti
    ForInst(String),
    // Should only be used with AnnotateMulti
    ForValues(String),
    Import,
    InstRule(String),
    // (State type, init, cond, step, finish)
    Loopify(Ident, Ident, Ident, Ident, Ident, Ident),
    Phantom,
    Recursive,
    // Should only be used with AnnotateMulti
    ShouldFail,
    Total,
    Verify,
}

fn path_to_one_str(p: &Path) -> Option<String> {
    if p.segments.len() == 1 {
        Some(p.segments.first().unwrap().ident.to_string())
    } else {
        None
    }
}

impl RvnItemAttr {
    fn is_primary(&self) -> bool { use RvnItemAttr::*; match self {
        Annotate(..) | AnnotateMulti | Assume | AssumeFor(..)
            | Declare | Define | Falsify | Import | Loopify(..)
            | Verify => true,
        _ => false,
    }}

    fn refer_text(&self) -> &'static str {
        use RvnItemAttr::*;
        match self {
            Annotate(..) => "#[annotate(..)]",
            AnnotateMulti => "#[annotate_multi]",
            Assume => "#[assume]",
            AssumeFor(..) => "#[assume(..)]",
            Declare => "#[declare]",
            Define => "#[define]",
            Falsify => "#[falsify]",
            ForCall(..) => "#[for_call(..)]",
            ForInst(..) => "#[for_inst(..)]",
            ForValues(..) => "#[for_values(..)]",
            Import => "#[import]",
            InstRule(..) => "#[for_type(..)]",
            Loopify(..) => "#[loopify(..)]",
            Phantom => "#[phantom]",
            Recursive => "#[recursive]",
            ShouldFail => "#[should_fail]",
            Total => "#[total]",
            Verify => "#[verify]",
        }
    }

    fn explain_context_requirement(&self) -> String {
        use RvnItemAttr::*;
        let rt = self.refer_text();
        match self {
            Annotate(..) | AnnotateMulti | Assume | AssumeFor(..) | Falsify | Loopify(..) | Verify => format!("{} should only be used as the first ravencheck attribute on a 'fn' item", rt),
            Declare | Define => format!("{} should only be used as the first ravencheck attribute on a 'fn', 'type', 'struct', or 'enum' item.", rt),
            ForCall(..) | ForInst(..) | ForValues(..) => format!("{} should only be used under {} on a 'fn' item", rt, AnnotateMulti.refer_text()),
            Import => format!("{} should only be used as the first ravencheck attribute on a 'use' item", rt),
            InstRule(..) => format!("{} should only be used under {} on a 'fn' item", rt, Assume.refer_text()),
            Phantom => format!("{} should only be used under {} or {}, on a 'fn', 'type', or 'struct', or 'enum' item.", rt, Declare.refer_text(), Define.refer_text()),
            Recursive => format!("{} should only be used under {} on a 'fn' item.", rt, Define.refer_text()),
            ShouldFail => format!("{} should only be used under {} on a 'fn' item.", rt, AnnotateMulti.refer_text()),
            Total => format!("{}, should only be used under {} or {} on a 'fn' item.", rt, Declare.refer_text(), Define.refer_text()),
        }
    }

    fn under_annotate_multi(attrs: &Vec<Self>) -> bool {
        attrs.iter().any(|a| match a { Self::AnnotateMulti => true, _ => false })
    }

    fn under_assume(attrs: &Vec<Self>) -> bool {
        attrs.iter().any(|a| match a { Self::Assume => true, _ => false })
    }

    fn under_declare(attrs: &Vec<Self>) -> bool {
        attrs.iter().any(|a| match a { Self::Declare => true, _ => false })
    }

    fn under_define(attrs: &Vec<Self>) -> bool {
        attrs.iter().any(|a| match a { Self::Define => true, _ => false })
    }

    fn from_attr_context(
        attr: &Attribute,
        item: SynItemTag,
        rvn_attrs: &Vec<RvnItemAttr>
    ) -> Result<Self, Result<(), SynError>> {
        use RvnItemAttr::*;

        let span = attr.span();

        let error = |e: &str| Err(Err(SynError::new(span.clone(), e)));
        let error2 = |e: &str| Err(Err(SynError::new(span.clone(), e)));
        let pass = || Err(Ok(()));
        let ret = |a: RvnItemAttr| Ok(a);

        // First, attempt to parse out a ravencheck attribute. If the
        // attribute is not recognized, pass it on.
        let attr = match &attr.meta {
            Meta::Path(p) if p.segments.len() == 1 => {
                match path_to_one_str(p).as_deref() {
                    Some("annotate") => error("This attribute needs arguments, for example: #[annotate(foo(a,b) => c)]")?,
                    Some("annotate_multi") => AnnotateMulti,
                    Some("assume") => Assume,
                    Some("declare") => Declare,
                    Some("define") => Define,
                    Some("define_rec") => error("#[define_rec] has been replaced by #[define] followed by #[recursive]")?,
                    Some("falsify") => RvnItemAttr::Falsify,
                    Some("import") => RvnItemAttr::Import,
                    Some("loopify") => error("This attribute needs arguments.")?,
                    Some("phantom") => RvnItemAttr::Phantom,
                    Some("recursive") => RvnItemAttr::Recursive,
                    Some("should_fail") => RvnItemAttr::ShouldFail,
                    Some("total") => RvnItemAttr::Total,
                    Some("verify") => RvnItemAttr::Verify,
                    _ => pass()?,
                }
            }
            Meta::List(l) if l.path.segments.len() == 1 => {
                match path_to_one_str(&l.path).as_deref() {
                    Some("annotate") => Annotate(l.tokens.to_string()),
                    Some("assume") => AssumeFor(l.tokens.to_string()),
                    Some("assume_for") => error("#[assume_for(..)] has been replaced by #[assume(..)]")?,
                    Some("declare") => error("#[declare] should not have arguments.")?,
                    Some("define") => error("#[define] should not have arguments.")?,
                    Some("define_rec") => error("#[define_rec] has been replaced by #[define] followed by #[recursive]")?,
                    Some("falsify") => error("#[falsify] should not have arguments.")?,
                    Some("for_call") => ForCall(l.tokens.to_string()),
                    Some("for_inst") => ForInst(l.tokens.to_string()),
                    Some("for_type") => InstRule(l.tokens.to_string()),
                    Some("for_values") => ForValues(l.tokens.to_string()),
                    Some("import") => error("#[import] should not have arguments.")?,
                    Some("loopify") => {
                        let parser =
                            Punctuated
                            ::<Ident,syn::Token![,]>
                            ::parse_separated_nonempty;
                        let idents: Punctuated<Ident,Token![,]> = elab_error(
                            parser.parse2(l.tokens.clone()),
                            "the #[loopify(..)] attribute expects six Ident arguments"
                        ).map_err(Err)?;
                        let idents: Vec<Ident> = idents.iter().cloned().collect();
                        Loopify(
                            idents[0].clone(),
                            idents[1].clone(),
                            idents[2].clone(),
                            idents[3].clone(),
                            idents[4].clone(),
                            idents[5].clone(),
                        )
                    }
                    _ => pass()?,
                }
            }
            _ => pass()?,
        };

        // If a ravencheck attribute was found, check that its context
        // is valid.

        // First, check that the attribute appears under other
        // attributes if and only if it is not primary.
        if rvn_attrs.len() > 0 && attr.is_primary() {
            error(&format!(
                "{} appears under {}, but {}",
                attr.refer_text(),
                rvn_attrs[0].refer_text(),
                &attr.explain_context_requirement(),
            ))?;
        }
        if rvn_attrs.len() == 0 && !attr.is_primary() {
            error(&format!(
                "{} appears as the first attribute, but {}",
                attr.refer_text(),
                &attr.explain_context_requirement(),
            ))?;
        }

        // Then, check that the attr is used in the appropriate
        // context. Each match arm returns () if a valid combination
        // of attr, item, and context is found.
        use SynItemTag as Tag;
        match (&attr, item) {
            // Declare
            (Declare, Tag::Const | Tag::Fn | Tag::Struct | Tag::Type) => (),

            // Define
            (Define, Tag::Enum | Tag::Fn | Tag::Struct | Tag::Type) => (),

            // Primary attributes that go on 'fn' items.
            (Annotate(..) | AnnotateMulti | Assume | AssumeFor(..) | Falsify | Loopify(..) | Verify, Tag::Fn) => (),

            // Secondary attributes that go under 'annotate_multi'.
            (ForCall(..) | ForInst(..) | ForValues(..) | ShouldFail, Tag::Fn) if Self::under_annotate_multi(rvn_attrs) => (),

            // Import
            (Import, Tag::Use) => (),

            // Secondary attributes that go under 'assume'.
            (InstRule(..), _) if Self::under_assume(rvn_attrs) => (),

            // Phantom: under 'define' or 'declare'
            (Phantom, _) if Self::under_define(rvn_attrs) || Self::under_declare(rvn_attrs) => (),

            // Recursive: only on a 'fn' or 'enum' under 'define'.
            (Recursive, Tag::Fn | Tag::Enum) if Self::under_define(rvn_attrs) => (),
            // Total: only on a 'fn' under 'declare' or 'define'.
            (Total, Tag::Fn) if Self::under_declare(rvn_attrs) || Self::under_define(rvn_attrs) => (),

            // If no valid combinations have matched, then show the
            // user an error that explains the context requirement for
            // the attribute.
            _ => error2(&attr.explain_context_requirement())?,
        }

        ret(attr)
    }

    /// Remove any `RvnAttr`s found from the given `Vec` and return a
    /// new `Vec` containing them.
    fn extract_from_attrs(
        tag: SynItemTag,
        attrs: &mut Vec<Attribute>
    ) -> Result<Vec<RvnItemAttr>, SynError> {
        let mut out: Vec<RvnItemAttr> = Vec::new();
        let mut context: Vec<RvnItemAttr> = Vec::new();
        let mut cumulative_error: Option<SynError> = None;
        attrs.retain_mut(|attr| {
            match RvnItemAttr::from_attr_context(attr, tag, &context) {
                Ok(a) => {
                    context.push(a.clone());
                    out.push(a);
                    false
                }
                Err(Ok(())) => true,
                Err(Err(e)) => {
                    match &mut cumulative_error {
                        Some(e1) => {
                            e1.combine(e);
                            // cumulative_error = Some(e1.combine(e));
                        }
                        None => {
                            cumulative_error = Some(e);
                        }
                    }
                    false
                }
            }
        });

        match cumulative_error {
            Some(e) => Err(e),
            None => Ok(out),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ShouldPanic {
    No,
    Yes,
    YesWithText(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RccCommand {
    Annotate(String, ItemFn),
    AnnotateMulti(bool, Vec<String>, Vec<String>, Vec<String>, ItemFn),
    Assume(Vec<String>, ItemFn),
    AssumeFor(String, ItemFn),
    /// The first boolean is `true` if this is a phantom
    /// declaration. The second is `true` if this should get a
    /// totality axiom.
    Declare(Item, bool, bool),
    DeclareType(Ident, usize),
    /// The first boolean is `true` if this is a phantome definition,
    /// and the second boolean is `true` if this is a recursive
    /// definition. The final boolean is `true` if this should get a
    /// totality axiom (which only makes sense if it's recursive).
    Define(Item, bool, bool, bool),
    Import(ItemUse),
    /// The boolean is `true` if this should be verified, and `false`
    /// if this should be falsified.
    Goal(bool, ItemFn),
    /// Set solver to this program, with no args.
    SetSolverProgram(String),
    /// Add this arg to the solver config.
    AddSolverArg(String),
}

impl RccCommand {
    fn mk_declare_define(
        ras: Vec<RvnItemAttr>,
        item: Item,
        define: bool,
    ) -> (Vec<Self>, Option<Item>) {
        let mut phantom = false;
        let mut recursive = false;
        let mut total = false;
        for a in ras { match a {
            RvnItemAttr::Phantom => { phantom = true; },
            RvnItemAttr::Recursive if define => { recursive = true; },
            RvnItemAttr::Total => { total = true; },
            a => panic!(
                "Unexpected {:?} under #[{}]",
                a,
                if define { "define"} else { "declare" },
            ),
        }}
        let ret_item = if !phantom {
            Some(item.clone())
        } else {
            None
        };
        if define {
            (vec![Self::Define(item, phantom, recursive, total)], ret_item)
        } else {
            (vec![Self::Declare(item, phantom, total)], ret_item)
        }
    }

    fn mk_loop(
        state_type: Ident,
        cond_type: Ident,
        init: Ident,
        comp: Ident,
        step: Ident,
        finish: Ident,
        item: ItemFn,
    ) -> (Vec<Self>, Option<Item>) {
        // The given ItemFn should have an empty body, which we will fill in two ways.
        assert!(
            item.block.stmts.len() == 0,
            "loopify function stub should have empty body",
        );

        // Get names of function args.
        //
        // This fails if args have complex patterns like _ or (a,b).
        let arg_names: Vec<Ident> = item.sig.inputs
            .iter()
            .map(|a| match a {
                FnArg::Typed(a) => match a.pat.as_ref() {
                    Pat::Ident(p) => Some(p.ident.clone()),
                    _ => None,
                }
                _ => None,
            })
            .collect::<Option<Vec<Ident>>>()
            .expect("loopify function arg names should be simple idents, not complex patterns");

        let wrapper_name = item.sig.ident.clone();
        let tail_rec_name = Ident::new(&format!("{}_tail_rec", wrapper_name), Span::call_site());

        let tail_rec_item: Item = parse_quote! {
            fn #tail_rec_name(s: #state_type) -> #state_type {
                match #comp(&s) {
                    Option::<#cond_type>::Some(c) => {
                        let s2 = #step(c, s);
                        #tail_rec_name(s2)
                    }
                    Option::<#cond_type>::None => s
                }
            }
        };
        let mut wrapper_item = item.clone();
        wrapper_item.block.stmts.push(parse_quote! {
            let s_init = #init(#(#arg_names),*);
        });
        wrapper_item.block.stmts.push(parse_quote! {
            let s_final = #tail_rec_name(s_init);
        });
        wrapper_item.block.stmts.push(Stmt::Expr(
            parse_quote! { #finish(s_final) },
            None,
        ));
        
        let mut loop_item = item;
        loop_item.block.stmts.push(parse_quote! {
            let mut s_mut = #init(#(#arg_names),*);
        });
        loop_item.block.stmts.push(parse_quote! {
            while let Some(c) = #comp(&s_mut) {
                s_mut = #step(c, s_mut);
            }
        });
        loop_item.block.stmts.push(Stmt::Expr(
            parse_quote! { #finish(s_mut) },
            None,
        ));
        // println!("Loop: {}", quote!{#loop_item});
        // println!("Stepper: {}", quote!{#tail_rec_item});
        // println!("Rec: {}", quote!{#wrapper_item});

        // let ret_item = if !phantom {
        //     Some(item.clone())
        // } else {
        //     None
        // };
        // if define {
        //     (Some(Self::Define(item, phantom, recursive, total)), ret_item)
        // } else {
        //     (Some(Self::Declare(item, phantom, total)), ret_item)
        // }
        let commands = vec![
            Self::Define(tail_rec_item, true, true, false),
            Self::Define(Item::Fn(wrapper_item), true, false, false),
        ];
        (commands, Some(Item::Fn(loop_item)))
    }

    fn mk_goal(
        ras: Vec<RvnItemAttr>,
        item: Item,
        should_be_valid: bool,
    ) -> (Vec<Self>, Option<Item>) {
        let attr_str = if should_be_valid {
            "#[verify]"
        } else {
            "#[falsify]"
        };
        for attr in ras {
            match attr {
                a => panic!("{:?} should not appear after {attr_str} on an item.", a),
            }
        }
        let item = match item {
            Item::Fn(i) => i,
            item => panic!(
                "You should not use {attr_str} on non-fn items, but you used it on {:?}",
                item,
            ),
        };
        (vec![Self::Goal(should_be_valid, item)], None)
    }

    /// Attempt to extract `RccCommand`s from an [`Item`], also
    /// returning the original (possibly modified) [`Item`] if it
    /// should remain in the module and be passed along to the Rust
    /// compiler.
    fn from_item(
        mut item: Item
    ) -> Result<(Vec<RccCommand>, Option<Item>), SynError> {
        use RvnItemAttr::*;

        // let ras = RvnItemAttr::extract_from_item(&mut item)?;

        let ras = match SynItemTag::tag_attrs(&mut item) {
            Some((i, attrs)) => RvnItemAttr::extract_from_attrs(i, attrs)?,
            None => Vec::new(),
        };

        // If there are no Ravencheck attrs, return the item
        // unchanged.
        if ras.len() == 0 {
            return Ok((Vec::new(), Some(item)));
        }
        let mut ras = VecDeque::from(ras);
        match ras.pop_front().unwrap() {
            Annotate(call) => match item {
                Item::Fn(i) => {
                    let c = RccCommand::Annotate(call, i);
                    Ok((vec![c], None))
                }
                item => Err(SynError::new(item.span(), "The #[annotate(..)] attribute should only be used on fn items.")),
                // item => panic!("Can't use #[annotate(..)] on {:?}", item),
            }
            AnnotateMulti => match item {
                Item::Fn(i) => {
                    let mut call_lines = Vec::new();
                    let mut inst_lines = Vec::new();
                    let mut value_lines = Vec::new();
                    let mut should_fail = false;
                    for a in ras { match a {
                        RvnItemAttr::ForCall(c) => { call_lines.push(c); },
                        RvnItemAttr::ForInst(i) => { inst_lines.push(i); },
                        RvnItemAttr::ForValues(l) => { value_lines.push(l); },
                        RvnItemAttr::ShouldFail => { should_fail = true; },
                        a => panic!(
                            "Unexpected {:?} on '{}'",
                            a,
                            i.sig.ident
                        ),
                    }}
                    let c = RccCommand::AnnotateMulti(
                        should_fail,
                        value_lines,
                        call_lines,
                        inst_lines,
                        i
                    );
                    Ok((vec![c], None))
                }
                item => Err(SynError::new(item.span(), "The #[annotate_multi(..)] attribute should only be used on fn items.")),
            }
            Assume => match item {
                Item::Fn(i) => {
                    let mut rules = Vec::new();
                    for a in ras { match a {
                        RvnItemAttr::InstRule(r) => { rules.push(r); },
                        a => panic!(
                            "Unexpected {:?} on '{}'",
                            a,
                            i.sig.ident
                        ),
                    }}
                    let c = RccCommand::Assume(rules, i);
                    Ok((vec![c], None))
                }
                item => Err(SynError::new(item.span(), "The #[assume] attribute should only be used on fn items.")),
            }
            AssumeFor(call) => match item {
                Item::Fn(i) => {
                    let c = RccCommand::AssumeFor(call, i);
                    Ok((vec![c], None))
                }
                item => Err(SynError::new(item.span(), "The #[assume(..)] attribute should only be used on fn items.")),
            }
            Declare => Ok(Self::mk_declare_define(Vec::from(ras), item, false)),
            Define => Ok(Self::mk_declare_define(Vec::from(ras), item, true)),
            Falsify => Ok(Self::mk_goal(Vec::from(ras), item, false)),
            Import => match item {
                Item::Use(i) => {
                    let c = RccCommand::Import(i.clone());
                    Ok((vec![c], Some(Item::Use(i))))
                }
                item => panic!("Can't use #[import] on {:?}", item),
            }
            InstRule(_) =>
                panic!("#[for_type(..)] should only appear under #[assume]"),
            Loopify(st,ct,i,c,s,f) => match item {
                Item::Fn(item) => Ok(Self::mk_loop(st,ct,i,c,s,f,item)),
                _ => panic!("#[loopify(..)] can only be used on a fn item"),
            }
            Phantom =>
                panic!("#[phantom] should only appear under #[declare] or #[define]"),
            Verify => Ok(Self::mk_goal(Vec::from(ras), item, true)),
            a => todo!("other attrs for from_item: {:?}", a),
        }
    }

    fn extract_from_items(items: &mut Vec<Item>) -> Result<Vec<Self>, SynError> {
        let mut commands: Vec<Self> = Vec::new();
        let mut items_out: Vec<Item> = Vec::new();
        for item in items.clone() {
            let (mut c,i) = Self::from_item(item)?;
            commands.append(&mut c);
            // if let Some(c) = c {
            //     commands.push(c);
            // }
            if let Some(i) = i {
                items_out.push(i);
            }
        }
        *items = items_out;
        Ok(commands)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum GenMode {
    Check,
    Export,
}

struct RvnMod {
    commands: Vec<RccCommand>,
    mode: GenMode,
    should_panic: ShouldPanic,
    source_hash: u64,
    use_env_logger: bool,
}

fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

fn elab_error<A>(
    a: Result<A, SynError>,
    msg: &str,
) -> Result<A, SynError> {
    match a {
        Ok(v) => Ok(v),
        Err(mut e) => {
            e.combine(SynError::new(e.span(), msg));
            Err(e)
        }
    }
}

fn replace_error<A>(
    a: Result<A, SynError>,
    span: Span,
    msg: &str,
) -> Result<A, SynError> {
    match a {
        Ok(v) => Ok(v),
        Err(_e) => Err(SynError::new(span, msg)),
    }
}

impl RvnMod {
    fn new_check() -> Self {
        Self {
            commands: Vec::new(),
            mode: GenMode::Check,
            should_panic: ShouldPanic::No,
            source_hash: 0,
            use_env_logger: false,
        }
    }

    fn new_export() -> Self {
        Self {
            commands: Vec::new(),
            mode: GenMode::Export,
            should_panic: ShouldPanic::No,
            source_hash: 0,
            use_env_logger: false,
        }
    }

    fn is_export(&self) -> bool {
        match self.mode {
            GenMode::Check => false,
            GenMode::Export => true,
        }
    }

    fn extract_from_toplevel_attrs(
        &mut self,
        attrs: &mut Vec<Attribute>,
    ) -> Result<(), SynError> {
        let mut errs = Vec::new();

        attrs.retain_mut(|attr| {
            match self.from_toplevel_attr(attr) {
                Ok(should_retain) => should_retain,
                Err(e) => {
                    errs.push(e);
                    // Doesn't matter what this value is, since we are
                    // going to throw a compile_error.
                    true
                }
            }
        });

        match errs.pop() {
            Some(mut e) => {
                for e1 in errs {
                    e.combine(e1);
                }
                Err(e)
            }
            None => Ok(()),
        }
    }

    /// Returns `true` if the `Attribute` should be retained, or
    /// `false` if it should be erased.
    fn from_toplevel_attr(
        &mut self,
        attr: &Attribute,
    ) -> Result<bool, SynError> {
        match &attr.meta {
            Meta::List(l) if l.path.segments.len() == 1 => {
                match path_to_one_str(&l.path).as_deref() {
                    Some("add_solver_args") => {
                        let parser =
                            Punctuated
                            ::<LitStr,syn::Token![,]>
                            ::parse_separated_nonempty;

                        let args = replace_error(
                            parser.parse2(l.tokens.clone()),
                            attr.span(),
                            "The #[add_solver_args(..)] attribute expects one or more strings as arguments",
                        )?;

                        for a in args.into_iter() {
                            self.commands.push(RccCommand::AddSolverArg(a.value()));
                        }

                        // Return false so that the attribute is
                        // erased before passing on to the Rust
                        // toolchain.
                        Ok(false)
                    }
                    Some("set_solver") => {
                        let parser =
                            Punctuated
                            ::<LitStr,syn::Token![,]>
                            ::parse_separated_nonempty;

                        let args = replace_error(
                            parser.parse2(l.tokens.clone()),
                            attr.span(),
                            "The #[set_solver(..)] attribute expects one or more strings as arguments: the first is the solver name, and the rest are the solver arguments",
                        )?;

                        let mut first = true;
                        for a in args.into_iter() {
                            if first {
                                self.commands.push(RccCommand::SetSolverProgram(a.value()));
                                first = false;
                            } else {
                                self.commands.push(RccCommand::AddSolverArg(a.value()));
                            }
                        }

                        // Return false so that the attribute is
                        // erased before passing on to the Rust
                        // toolchain.
                        Ok(false)
                    }
                    Some("declare_types") => {
                        let parser =
                            Punctuated
                            ::<Path,syn::Token![,]>
                            ::parse_separated_nonempty;

                        let types = replace_error(
                            parser.parse2(l.tokens.clone()),
                            attr.span(),
                            "The #[declare_types(..)] attribute expects one or more types as arguments",
                        )?;

                        for mut p in types.into_iter() {
                            let seg = p.segments.pop().unwrap().into_value();
                            let arity = match seg.arguments {
                                PathArguments::None => 0,
                                PathArguments::AngleBracketed(a) => a.args.len(),
                                PathArguments::Parenthesized(..) => {
                                    return Err(SynError::new(
                                        seg.span(),
                                        format!("Declared types should get angle-bracketed arguments <..>, but {} got parenthesized arguments", seg.ident),
                                    ))
                                }
                            };

                            self.commands.push(
                                RccCommand::DeclareType(seg.ident, arity)
                            );
                        }

                        // Return false so that the attribute is
                        // erased before passing on to the Rust
                        // toolchain.
                        Ok(false)
                    }
                    Some("rvn_should_panic") => {
                        let s: String = syn::parse2::<LitStr>(l.tokens.clone())
                            .unwrap()
                            .value();
                        self.should_panic = ShouldPanic::YesWithText(s);
                        Ok(false)
                    }
                    _ => Ok(true),
                }
            }
            Meta::Path(p) if p.segments.len() == 1 => {
                match path_to_one_str(p).as_deref() {
                    Some("rvn_should_panic") => {
                        self.should_panic = ShouldPanic::Yes;
                        Ok(false)
                    }
                    Some("log_solver") => {
                        self.use_env_logger = true;
                        Ok(false)
                    }
                    _ => Ok(true),
                }
            }
            _ => Ok(true),
        }
    }

}

fn generate_stmts(commands: &Vec<RccCommand>, mode: GenMode) -> Vec<Stmt> {
    let mut out = Vec::new();
    for c in commands {
        match c {
            RccCommand::AddSolverArg(arg) => {
                match mode {
                    GenMode::Check => {
                        let arg_str = quote!{#arg};
                        let s: Stmt = syn::parse2(quote! {
                            rcc.add_solver_arg(#arg_str);
                        }).unwrap();
                        out.push(s);
                    }
                    GenMode::Export => {}
                }
            }
            RccCommand::DeclareType(ident, arity) => {
                let ident_str = quote!{#ident}.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_toplevel_type(#ident_str, #arity);
                }).unwrap();
                out.push(s);
            }
            RccCommand::Annotate(call_str, item_fn) => {
                let item_str = quote!{ #item_fn }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_fn_annotate(#call_str, #item_str).unwrap();
                }).unwrap();
                out.push(s);
            }
            RccCommand::AnnotateMulti(should_fail, value_strs, call_strs, inst_strs, item_fn) => {
                let item_str = quote!{ #item_fn }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_fn_annotate_multi(
                        #should_fail,
                        [#(#value_strs),*],
                        [#(#call_strs),*],
                        [#(#inst_strs),*],
                        #item_str
                    ).unwrap();
                }).unwrap();
                out.push(s);
            }
            RccCommand::Assume(rules, item_fn) => {
                let item_str = quote!{ #item_fn }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_fn_assume([#(#rules),*], #item_str);
                }).unwrap();
                out.push(s);
            }
            RccCommand::AssumeFor(call_str, item_fn) => {
                let item_str = quote!{ #item_fn }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_fn_assume_for(#call_str, #item_str);
                }).unwrap();
                out.push(s);
            }
            // The effect of 'is_phantom' has already been handled at
            // the attribute extraction stage.
            RccCommand::Declare(item, _is_phantom, is_total) => {
                let item_str = quote!{ #item }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_item_declare(#item_str, #is_total);
                }).unwrap();
                out.push(s)
            }
            RccCommand::Define(item, _is_phantom, is_rec, is_total) => {
                let item_str = quote!{ #item }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_item_define(#item_str, #is_rec, #is_total);
                }).unwrap();
                out.push(s)
            }
            RccCommand::Import(item) => {
                let segs = use_tree_to_path(item.tree.clone());
                let mut punct = Punctuated::<PathSegment, Token![::]>::new();
                for s in segs {
                    punct.push(s);
                }
                let path = Path { leading_colon: None, segments: punct };
                let s: Stmt = syn::parse_quote! {
                    rcc = #path::ravencheck_exports::apply_exports(rcc);
                };
                out.push(s);
            }
            RccCommand::Goal(should_be_valid, item_fn) => {
                let item_fn = item_fn.clone();
                match mode {
                    GenMode::Check => {
                        let item_fn_str = quote!{ #item_fn }.to_string();
                        let s: Stmt = syn::parse2(quote! {
                            rcc.reg_fn_goal(#should_be_valid, #item_fn_str);
                        }).unwrap();
                        out.push(s);
                    }
                    GenMode::Export => {}
                }
            }
            RccCommand::SetSolverProgram(name) => {
                match mode {
                    GenMode::Check => {
                        let name_str = quote!{#name};
                        let s: Stmt = syn::parse2(quote! {
                            rcc.set_solver(#name_str);
                        }).unwrap();
                        out.push(s);
                    }
                    GenMode::Export => {}
                }
            }
        }
    }
    out
}

fn use_tree_to_path(t: UseTree) -> Vec<PathSegment> {
    match t {
        UseTree::Path(p) => {
            let i = p.ident.clone();
            let mut rest = use_tree_to_path(*p.tree);
            rest.insert(0, PathSegment{
                ident: i,
                arguments: PathArguments::None,
            });
            rest
        },
        UseTree::Glob(..) => Vec::new(),
        UseTree::Group(..) => Vec::new(),
        UseTree::Name(..) => Vec::new(),
        t => panic!("cannot #[import] use-tree with {:?} node in it", t),
    }
}

fn result_to_tokens(r: Result<TokenStream, SynError>) -> TokenStream {
    match r {
        Ok(t) => t,
        Err(e) => e.into_compile_error().into(),
    }
}

#[proc_macro_attribute]
pub fn export_module(attrs: TokenStream, input: TokenStream) -> TokenStream {
    result_to_tokens(
        process_module(attrs, input, RvnMod::new_export())
    )
}

#[proc_macro_attribute]
pub fn check_module(attrs: TokenStream, input: TokenStream) -> TokenStream {
    result_to_tokens(
        process_module(attrs, input, RvnMod::new_check())
    )
}

/// This function returns a Result, in which both the Ok and Err types
/// are TokenStreams. The Ok output should contain a successful
/// compilation output, while the Err output should contain a
/// 'compile_error!(..)'.
///
/// Both outputs should be handled by just passing them on as the
/// output of the macro. They are only distinguished so that we can
/// use '?' syntax to short-circuit.
fn process_module(
    attrs: TokenStream,
    input: TokenStream,
    mut rvn: RvnMod,
) -> Result<TokenStream, SynError> {

    rvn.source_hash = calculate_hash(&input.to_string());

    // The macro needs to name the crate that CheckedSig comes from,
    // and that will be different depending on the context that
    // check_module is called in.
    let cratename: Ident = if attrs.is_empty() {
        Ident::new("ravencheck", Span::call_site())
    } else {
        // The parse_any parser is needed since the crate name could
        // be a normal ident or a keyword (like 'crate' or 'super').
        let parser = Ident::parse_any;
        parser.parse(attrs).expect("parse crate name")
    };

    let mut m: ItemMod = match syn::parse(input) {
        Ok(m) => Ok(m),
        Err
            (mut e) => {
            let attr_name = match rvn.mode {
                GenMode::Check => "check_module",
                GenMode::Export => "export_module",
            };
            e.combine(
                SynError::new(
                    e.span(),
                    format!(
                        "The '{attr_name}' attribute can only be applied to a module item."
                    ),
                )
            );
            Err(e)
        }
    }?;

    // Handle commands within the top-level attributes
    rvn.extract_from_toplevel_attrs(&mut m.attrs)?;

    // Handle per-item commands within the module
    match &mut m.content {
        Some((_,items)) => {

            // extract_items(items, &mut rcc_items);
            rvn.commands.append(
                &mut RccCommand::extract_from_items(items)?
            );

            let mut test_stmts: Vec<Stmt> =
                generate_stmts(&rvn.commands, GenMode::Check);
            test_stmts.push(
                syn::parse2(quote!{
                    rcc.check_goals();
                }).unwrap()
            );

            let mut test: ItemFn = if rvn.use_env_logger {
                syn::parse_quote! {
                    #[test]
                    fn check_properties() {
                        let _ = env_logger::builder().is_test(true).try_init();
                        let mut rcc = Rcc::new();

                        // Interpolate 'stmts' here
                        #(#test_stmts)*
                    }
                }
            } else {
                syn::parse_quote! {
                    #[test]
                    fn check_properties() {
                        let mut rcc = Rcc::new();

                        // Interpolate 'stmts' here
                        #(#test_stmts)*
                    }
                }
            };

            match &rvn.should_panic {
                ShouldPanic::No => {},
                ShouldPanic::Yes => {
                    let parser = Attribute::parse_outer;
                    let mut a = parser.parse_str("#[should_panic]").unwrap();
                    test.attrs.push(a.pop().unwrap());
                }
                ShouldPanic::YesWithText(s) => {
                    let parser = Attribute::parse_outer;
                    let tokens = quote!{ #[should_panic(expected = #s)] };
                    let mut a = parser.parse2(tokens).unwrap();
                    test.attrs.push(a.pop().unwrap());
                }
            }

            let test_s = Item::Fn(test);
            // println!("the test: {}", quote!{ #test_s });

            let test_mod = quote! {
                #[cfg(test)]
                mod ravencheck_tests {
                    use #cratename::Rcc;

                    #test_s
                }
            };

            // println!("Here is the test module content:");
            // println!("{}", test_mod);

            items.push(syn::parse(test_mod.into()).expect("parse test mod"));

            if rvn.is_export() {
                let export_stmts: Vec<Stmt> =
                    generate_stmts(&rvn.commands, GenMode::Export);

                let hash = rvn.source_hash;
                let export_mod = quote! {
                    pub mod ravencheck_exports {
                        use #cratename::Rcc;

                        pub fn apply_exports(mut rcc: Rcc) -> Rcc {
                            if !rcc.seen_hashes.contains(&#hash) {
                                rcc.seen_hashes.insert(#hash);
                                #(#export_stmts)*
                            }
                            rcc
                        }
                    }
                };

                // println!("Here is the export module content:");
                // println!("{}", export_mod);
                items.push(syn::parse(export_mod.into()).expect("parse export mod"));
            }
        }
        None => {}
    }
    let out = quote! {
        #m
    };
    Ok(out.into())
}
