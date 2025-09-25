use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;

use syn::{
    Attribute,
    Ident,
    Item,
    ItemFn,
    ItemMod,
    ItemUse,
    Meta,
    Path,
    PathArguments,
    PathSegment,
    punctuated::Punctuated,
    Stmt,
    Token,
    UseTree,
};
use syn::ext::IdentExt;
use syn::parse::Parser;

use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, PartialEq)]
enum RvnItemAttr {
    Annotate(String),
    Assume,
    AssumeFor(String),
    Declare,
    Define,
    Falsify,
    Import,
    InstRule(String),
    Phantom,
    Recursive,
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
                    Some("assume") => Some(RvnItemAttr::Assume),
                    Some("declare") => Some(RvnItemAttr::Declare),
                    Some("define") => Some(RvnItemAttr::Define),
                    Some("define_rec") => panic!("#[define_rec] has been replaced by #[define] followed by #[recursive]"),
                    Some("falsify") => Some(RvnItemAttr::Falsify),
                    Some("import") => Some(RvnItemAttr::Import),
                    Some("phantom") => Some(RvnItemAttr::Phantom),
                    Some("recursive") => Some(RvnItemAttr::Recursive),
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
                    Some("for_type") => Some(RvnItemAttr::InstRule(l.tokens.to_string())),
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
            // // item => todo!("RvnItemAttr::extract_from_item for {:?}", item),
            // Assume anything we haven't listed here is something
            // that we totally ignore.
            _item => Vec::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RccCommand {
    Annotate(String, ItemFn),
    Assume(Vec<String>, ItemFn),
    AssumeFor(String, ItemFn),
    /// The boolean is `true` if this is a phantom declaration.
    Declare(Item, bool),
    DeclareType(Ident, usize),
    /// The first boolean is `true` if this is a phantome definition,
    /// and the second boolean is `true` if this is a recursive
    /// definition.
    Define(Item, bool, bool),
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
    ) -> (Option<Self>, Option<Item>) {
        let mut phantom = false;
        let mut recursive = false;
        for a in ras { match a {
            RvnItemAttr::Phantom => { phantom = true; },
            RvnItemAttr::Recursive if define => { recursive = true; },
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
            (Some(Self::Define(item, phantom, recursive)), ret_item)
        } else {
            (Some(Self::Declare(item, phantom)), ret_item)
        }
    }

    fn mk_goal(
        ras: Vec<RvnItemAttr>,
        item: Item,
        should_be_valid: bool,
    ) -> (Option<Self>, Option<Item>) {
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
        (Some(Self::Goal(should_be_valid, item)), None)
    }

    /// Attempt to extract a `RccCommand` from an [`Item`], also
    /// returning the original (possibly modified) [`Item`] if it
    /// should remain in the module and be passed along to the Rust
    /// compiler.
    fn from_item(mut item: Item) -> (Option<RccCommand>, Option<Item>) {
        use RvnItemAttr::*;

        let ras = RvnItemAttr::extract_from_item(&mut item);

        // If there are no Ravencheck attrs, return the item
        // unchanged.
        if ras.len() == 0 {
            return (None, Some(item));
        }
        let mut ras = VecDeque::from(ras);
        match ras.pop_front().unwrap() {
            Annotate(call) => match item {
                Item::Fn(i) => {
                    let c = RccCommand::Annotate(call, i);
                    (Some(c), None)
                }
                item => panic!("Can't use #[annotate(..)] on {:?}", item),
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
                    (Some(c), None)
                }
                item => panic!("Can't use #[assume] on {:?}", item),
            }
            AssumeFor(call) => match item {
                Item::Fn(i) => {
                    let c = RccCommand::AssumeFor(call, i);
                    (Some(c), None)
                }
                item => panic!("Can't use #[assume(..)] on {:?}", item),
            }
            Declare => Self::mk_declare_define(Vec::from(ras), item, false),
            Define => Self::mk_declare_define(Vec::from(ras), item, true),
            Falsify => Self::mk_goal(Vec::from(ras), item, false),
            Import => match item {
                Item::Use(i) => {
                    let c = RccCommand::Import(i.clone());
                    (Some(c), Some(Item::Use(i)))
                }
                item => panic!("Can't use #[import] on {:?}", item),
            }
            InstRule(_) =>
                panic!("#[for_type(..)] should only appear under #[assume]"),
            Phantom =>
                panic!("#[phantom] should only appear under #[declare] or #[define]"),
            Verify => Self::mk_goal(Vec::from(ras), item, true),
            _ => todo!("other attrs for from_item"),
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
            let (c,i) = Self::from_item(item);
            if let Some(c) = c {
                commands.push(c);
            }
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
            RccCommand::Declare(item, _is_phantom) => {
                let item_str = quote!{ #item }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_item_declare(#item_str);
                }).unwrap();
                out.push(s)
            }
            RccCommand::Define(item, _is_phantom, is_rec) => {
                let item_str = quote!{ #item }.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_item_define(#item_str, #is_rec);
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
                        #path::ravencheck_exports::apply_exports(&mut rcc);
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

                        pub fn apply_exports(rcc: &mut Rcc) {
                            #(#export_stmts)*
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
