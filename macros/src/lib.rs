use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;

use syn::{
    Attribute,
    FnArg,
    Ident,
    Item,
    ItemFn,
    ItemMod,
    ItemUse,
    Meta,
    Pat,
    Path,
    PathArguments,
    PathSegment,
    punctuated::Punctuated,
    Stmt,
    Token,
    UseTree,
    parse_quote,
};
use syn::ext::IdentExt;
use syn::parse::Parser;

use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, PartialEq)]
enum RvnItemAttr {
    Annotate(String),
    AnnotateMulti,
    Assume,
    AssumeFor(String),
    Declare,
    Define,
    Falsify,
    ForCall(String),
    ForInst(String),
    ForValues(String),
    Import,
    InstRule(String),
    // (State type, init, cond, step, finish)
    Loopify(Ident, Ident, Ident, Ident, Ident, Ident),
    Phantom,
    Recursive,
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
    fn try_from_attr(attr: &Attribute) -> Option<RvnItemAttr> {
        match &attr.meta {
            Meta::Path(p) if p.segments.len() == 1 => {
                match path_to_one_str(p).as_deref() {
                    Some("annotate") => panic!("#[annotate] needs arguments"),
                    Some("annotate_multi") => Some(RvnItemAttr::AnnotateMulti),
                    Some("assume") => Some(RvnItemAttr::Assume),
                    Some("declare") => Some(RvnItemAttr::Declare),
                    Some("define") => Some(RvnItemAttr::Define),
                    Some("define_rec") => panic!("#[define_rec] has been replaced by #[define] followed by #[recursive]"),
                    Some("falsify") => Some(RvnItemAttr::Falsify),
                    Some("import") => Some(RvnItemAttr::Import),
                    Some("phantom") => Some(RvnItemAttr::Phantom),
                    Some("recursive") => Some(RvnItemAttr::Recursive),
                    Some("should_fail") => Some(RvnItemAttr::ShouldFail),
                    Some("total") => Some(RvnItemAttr::Total),
                    Some("verify") => Some(RvnItemAttr::Verify),
                    _ => None,
                }
            }
            Meta::List(l) if l.path.segments.len() == 1 => {
                match path_to_one_str(&l.path).as_deref() {
                    Some("annotate") =>
                        Some(RvnItemAttr::Annotate(l.tokens.to_string())),
                    Some("assume") =>
                        Some(RvnItemAttr::AssumeFor(l.tokens.to_string())),
                    Some("assume_for") => {
                        panic!("#[assume_for(..)] has been replaced by #[assume(..)]")
                        // let fun_name: Ident = l.parse_args().unwrap();
                        // Some(RvnAttr::AssumeFor(fun_name.to_string()))
                    }
                    Some("for_call") =>
                        Some(RvnItemAttr::ForCall(l.tokens.to_string())),
                    Some("for_inst") =>
                        Some(RvnItemAttr::ForInst(l.tokens.to_string())),
                    Some("for_type") => Some(RvnItemAttr::InstRule(l.tokens.to_string())),
                    Some("for_values") =>
                        Some(RvnItemAttr::ForValues(l.tokens.to_string())),
                    Some("loopify") => {
                        let parser =
                            Punctuated
                            ::<Ident,syn::Token![,]>
                            ::parse_separated_nonempty;
                        // let types = parser
                        //     .parse2(l.tokens.clone())
                        //     .expect("the #[declare_types(..)] attribute expects one or more type names as arguments");
                        let idents: Punctuated<Ident,Token![,]> =
                            parser.parse2(l.tokens.clone())
                            .expect("the #[loopify(..)] attribute expects six Ident arguments");
                        let idents: Vec<Ident> = idents.iter().cloned().collect();
                        Some(RvnItemAttr::Loopify(
                            idents[0].clone(),
                            idents[1].clone(),
                            idents[2].clone(),
                            idents[3].clone(),
                            idents[4].clone(),
                            idents[5].clone(),
                        ))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Remove any `RvnAttr`s found from the given `Vec` and return a
    /// new `Vec` containing them.
    fn extract_from_attrs(attrs: &mut Vec<Attribute>) -> Vec<RvnItemAttr> {
        let mut out = Vec::new();
        attrs.retain_mut(|attr| {
            match RvnItemAttr::try_from_attr(attr) {
                Some(a) => {
                    out.push(a);
                    false
                }
                None => true,
            }
        });
        out
    }

    fn extract_from_item(item: &mut Item) -> Vec<RvnItemAttr> {
        match item {
            Item::Const(i) => Self::extract_from_attrs(&mut i.attrs),
            Item::Enum(i) => Self::extract_from_attrs(&mut i.attrs),
            Item::Fn(i) => Self::extract_from_attrs(&mut i.attrs),
            Item::Impl(_) => Vec::new(),
            Item::Mod(_) => Vec::new(),
            Item::Struct(i) => Self::extract_from_attrs(&mut i.attrs),
            Item::Type(i) => Self::extract_from_attrs(&mut i.attrs),
            Item::Use(i) => Self::extract_from_attrs(&mut i.attrs),
            // Assume anything we haven't listed here is something
            // that we totally ignore.
            _item => Vec::new(),
        }
    }
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
        assert!(
            ras.len() == 0,
            "#[verify] and #[falsify] should not have further attributes beneath them",
        );
        let item = match item {
            Item::Fn(i) => i,
            item => panic!(
                "should not use #[verify] or #[falsify] on {:?}",
                item,
            ),
        };
        (vec![Self::Goal(should_be_valid, item)], None)
    }

    /// Attempt to extract `RccCommand`s from an [`Item`], also
    /// returning the original (possibly modified) [`Item`] if it
    /// should remain in the module and be passed along to the Rust
    /// compiler.
    fn from_item(mut item: Item) -> (Vec<RccCommand>, Option<Item>) {
        use RvnItemAttr::*;

        let ras = RvnItemAttr::extract_from_item(&mut item);

        // If there are no Ravencheck attrs, return the item
        // unchanged.
        if ras.len() == 0 {
            return (Vec::new(), Some(item));
        }
        let mut ras = VecDeque::from(ras);
        match ras.pop_front().unwrap() {
            Annotate(call) => match item {
                Item::Fn(i) => {
                    let c = RccCommand::Annotate(call, i);
                    (vec![c], None)
                }
                item => panic!("Can't use #[annotate(..)] on {:?}", item),
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
                    (vec![c], None)
                }
                item => panic!("Can't use #[annotate_multi(..)] on {:?}", item),
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
                    (vec![c], None)
                }
                item => panic!("Can't use #[assume] on {:?}", item),
            }
            AssumeFor(call) => match item {
                Item::Fn(i) => {
                    let c = RccCommand::AssumeFor(call, i);
                    (vec![c], None)
                }
                item => panic!("Can't use #[assume(..)] on {:?}", item),
            }
            Declare => Self::mk_declare_define(Vec::from(ras), item, false),
            Define => Self::mk_declare_define(Vec::from(ras), item, true),
            Falsify => Self::mk_goal(Vec::from(ras), item, false),
            Import => match item {
                Item::Use(i) => {
                    let c = RccCommand::Import(i.clone());
                    (vec![c], Some(Item::Use(i)))
                }
                item => panic!("Can't use #[import] on {:?}", item),
            }
            InstRule(_) =>
                panic!("#[for_type(..)] should only appear under #[assume]"),
            Loopify(st,ct,i,c,s,f) => match item {
                Item::Fn(item) => Self::mk_loop(st,ct,i,c,s,f,item),
                _ => panic!("#[loopify(..)] can only be used on a fn item"),
            }
            Phantom =>
                panic!("#[phantom] should only appear under #[declare] or #[define]"),
            Verify => Self::mk_goal(Vec::from(ras), item, true),
            a => todo!("other attrs for from_item: {:?}", a),
        }
    }

    fn from_toplevel_attr(attr: &Attribute) -> Vec<Self> {
        let mut out = Vec::new();
        match &attr.meta {
            Meta::List(l) if l.path.segments.len() == 1 => {
                match path_to_one_str(&l.path).as_deref() {
                    Some("declare_types") => {
                        let parser =
                            Punctuated
                            ::<Path,syn::Token![,]>
                            ::parse_separated_nonempty;
                        let types = parser
                            .parse2(l.tokens.clone())
                            .expect("the #[declare_types(..)] attribute expects one or more type names as arguments");

                        for mut p in types.into_iter() {
                            let seg = p.segments.pop().unwrap().into_value();
                            let arity = match seg.arguments {
                                PathArguments::None => 0,
                                PathArguments::AngleBracketed(a) => a.args.len(),
                                PathArguments::Parenthesized(..) => panic!("declared types should get angle-bracketed arguments <..>, but {} got parenthesized arguments", seg.ident),
                            };

                            out.push(RccCommand::DeclareType(seg.ident, arity));
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        out
    }

    fn extract_from_toplevel_attrs(attrs: &mut Vec<Attribute>) -> Vec<Self> {
        let mut out = Vec::new();
        attrs.retain_mut(|attr| {
            let mut cs = Self::from_toplevel_attr(attr);
            if cs.len() > 0 {
                out.append(&mut cs);
                false
            } else {
                true
            }
        });
        out
    }

    fn extract_from_items(items: &mut Vec<Item>) -> Vec<Self> {
        let mut commands: Vec<Self> = Vec::new();
        let mut items_out: Vec<Item> = Vec::new();
        for item in items.clone() {
            let (mut c,i) = Self::from_item(item);
            commands.append(&mut c);
            // if let Some(c) = c {
            //     commands.push(c);
            // }
            if let Some(i) = i {
                items_out.push(i);
            }
        }
        *items = items_out;
        commands
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum GenMode {
    Check,
    Export,
}

fn generate_stmts(commands: &Vec<RccCommand>, mode: GenMode) -> Vec<Stmt> {
    let mut out = Vec::new();
    for c in commands {
        match c {
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
                let path_str = quote!{ #path }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    if rcc.touch_new_path(#path_str) {
                        rcc = #path::ravencheck_exports::apply_exports(rcc);
                    }
                }).unwrap();
                out.push(s);
            }
            RccCommand::Goal(should_be_valid, item_fn) => {
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

#[proc_macro_attribute]
pub fn export_module(attrs: TokenStream, input: TokenStream) -> TokenStream {
    process_module(attrs, input, true)
}

#[proc_macro_attribute]
pub fn check_module(attrs: TokenStream, input: TokenStream) -> TokenStream {
    process_module(attrs, input, false)
}

fn process_module(
    attrs: TokenStream,
    input: TokenStream,
    export: bool,
) -> TokenStream {

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

    let mut m: ItemMod = match syn::parse(input).expect("parse input") {
        Item::Mod(m) => m,
        i => panic!(
            "'check_module' macro should only be applied to a module, but it was applied to {:?}",
            i,
        ),
    };

    // Handle commands within the top-level attributes
    let mut commands =
        RccCommand::extract_from_toplevel_attrs(&mut m.attrs);
    // extract_top_level(&mut m.attrs, &mut rcc_items);

    // Handle per-item commands within the module
    match &mut m.content {
        Some((_,items)) => {
            
            // extract_items(items, &mut rcc_items);
            commands.append(
                &mut RccCommand::extract_from_items(items)
            );

            let mut test_stmts: Vec<Stmt> =
                generate_stmts(&commands, GenMode::Check);
            test_stmts.push(
                syn::parse2(quote!{
                    rcc.check_goals();
                }).unwrap()
            );

            let test: ItemFn = syn::parse((quote! {
                #[test]
                fn check_properties() {
                    let mut rcc = Rcc::new();

                    // Interpolate 'stmts' here
                    #(#test_stmts)*
                }
            }).into()).unwrap();

            let test_s = Item::Fn(test);

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

            if export {
                let export_stmts: Vec<Stmt> =
                    generate_stmts(&commands, GenMode::Export);

                let export_mod = quote! {
                    pub mod ravencheck_exports {
                        use #cratename::Rcc;

                        pub fn apply_exports(mut rcc: Rcc) -> Rcc {
                            #(#export_stmts)*
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
    out.into()
}
