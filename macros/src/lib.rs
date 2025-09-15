use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::ext::IdentExt;
use syn::{
    Attribute,
    Block,
    FnArg,
    GenericParam,
    Ident,
    Item,
    ItemFn,
    ItemMod,
    Meta,
    PatType,
    Path,
    PathArguments,
    PathSegment,
    ReturnType,
    Stmt,
    Token,
    Type,
    UseTree,
};


#[proc_macro]
pub fn verify(input: TokenStream) -> TokenStream {
    let mut args: Vec<syn::Expr> = syn::parse_macro_input!(input with Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated).into_iter().collect();
    let e = args.pop().unwrap();
    let sig = args.pop().unwrap();
    let out = quote! {
        (#sig).assert_valid(stringify!(#e));
    };
    out.into()
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RvnAttr {
    Annotate(String),
    Assume(Vec<(Type,Vec<Type>)>),
    AssumeFor(String),
    Declare,
    // (is_recursive, is_phantom)
    Define(bool,bool),
    Import,
    // (should_be_valid)
    Verify(bool),
}

fn path_to_one_str(p: &Path) -> String {
    assert!(p.segments.len() == 1);
    p.segments.first().unwrap().ident.to_string()
}

impl RvnAttr {
    fn try_from_attr(attr: &Attribute) -> Option<RvnAttr> {
        match &attr.meta {
            Meta::Path(p) if p.segments.len() == 1 => {
                match path_to_one_str(p).as_str() {
                    "assume" => Some(RvnAttr::Assume(Vec::new())),
                    "declare" => Some(RvnAttr::Declare),
                    "define" => Some(RvnAttr::Define(false,false)),
                    "define_rec" => Some(RvnAttr::Define(true,false)),
                    "phantom" => Some(RvnAttr::Define(false,true)),
                    "falsify" => Some(RvnAttr::Verify(false)),
                    "import" => Some(RvnAttr::Import),
                    "verify" => Some(RvnAttr::Verify(true)),
                    _ => None,
                }
            }
            Meta::List(l) if l.path.segments.len() == 1 => {
                match path_to_one_str(&l.path).as_str() {
                    "annotate" => {
                        let fun_name: Ident = l.parse_args().unwrap();
                        Some(RvnAttr::Annotate(fun_name.to_string()))
                    }
                    "assume" => {
                        let rule: Type = l.parse_args().unwrap();
                        match rule {
                            Type::Tuple(t) => {
                                let a = t.elems[0].clone();
                                match t.elems[1].clone() {
                                    Type::Tuple(bs) => {
                                        Some(RvnAttr::Assume(vec![(
                                            a,
                                            bs.elems.iter().cloned().collect(),
                                        )]))
                                    }
                                    b => {
                                        Some(RvnAttr::Assume(vec![(a,vec![b])]))
                                    }
                                }
                                // let b = t.elems[1].clone();
                                // Some(RvnAttr::Assume(vec![(a,b)]))
                            }
                            t => todo!("Can't handle inst rule {:?}", t),
                        }
                    }
                    "assume_for" => {
                        let fun_name: Ident = l.parse_args().unwrap();
                        Some(RvnAttr::AssumeFor(fun_name.to_string()))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

fn extract_rvn_attr(item: &mut Item) -> Option<RvnAttr> {
    match item {
        Item::Const(i) => pop_rvn_attr(&mut i.attrs),
        Item::Fn(i) => pop_rvn_attr(&mut i.attrs),
        Item::Struct(i) => pop_rvn_attr(&mut i.attrs),
        Item::Type(i) => pop_rvn_attr(&mut i.attrs),
        Item::Use(i) => pop_rvn_attr(&mut i.attrs),
        _ => None,
    }
}

fn pop_rvn_attr(attrs: &mut Vec<Attribute>) -> Option<RvnAttr> {
    let mut out = None;
    attrs.retain_mut(|attr| {
        match RvnAttr::try_from_attr(attr) {
            Some(ra) => {
                match &out {
                    Some(other) => panic!(
                        "only one ravencheck command should be used per item, but both {:?} and {:?} were used together",
                        other,
                        ra,
                    ),
                    None => {}
                }

                out = Some(ra);

                // Drop all ravencheck commands
                false
            }

            // Don't drop anything that wasn't a ravencheck command
            None => true, 
        }
    });

    out
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SigItem {
    Annotation(String, String, Block),
    Axiom(Block, Vec<Ident>, Vec<(Type,Vec<Type>)>),
    FunctionAxiom(String, String, Block),
    Goal(String, Block, bool),
    Import(Path),
    TypeAlias(Ident,Type),
    // The final bool is true if this is a recursive def
    DFun(Ident, Vec<Ident>, Vec<PatType>, Type, Block, bool),
    Type(Ident, usize),
    UFun(String, Vec<Ident>, Vec<PatType>, Type),
    UConst(String, Type),
}

impl SigItem {
    fn is_export(&self) -> bool {
        match self {
            Self::Goal(..) => false,
            _ => true,
        }
    }
    fn into_stmt(self) -> Stmt {
        match self {
            SigItem::Annotation(title,f,b) => {
                let b_tks = format!("{}", quote! { #b });
                syn::parse((quote! {
                    sig.add_checked_annotation(#title, #f, #b_tks);
                }).into()).unwrap()
            }
            SigItem::FunctionAxiom(_title,f,b) => {
                let b_tks = format!("{}", quote! { #b });
                syn::parse((quote! {
                    sig.add_annotation(#f, #b_tks);
                }).into()).unwrap()
            }
            SigItem::Axiom(b,tas,rules) => {
                let b_tks = format!("{}", quote! { #b });
                let tas: Vec<String> = tas.into_iter().map(|i| {
                    format!("{}", quote! { #i })
                }).collect();
                let rules: Vec<(String,_)> = rules.into_iter().map(|(a,bs)| {
                    let bs: Vec<String> = bs.into_iter().map(|b| format!("{}", quote! { #b })).collect();
                    (format!("{}", quote! { #a }),
                     quote! { vec![#(#bs),*] })
                }).collect();
                let rules: Vec<_> = rules.into_iter().map(|(a,b)| {
                    quote! { (#a, #b) }
                }).collect();
                syn::parse((quote! {
                    sig.add_axiom2(#b_tks, [#(#tas),*], [#(#rules),*]);
                }).into()).unwrap()
            }
            SigItem::Goal(title, b, should_be_valid) => {
                let b_tks = format!("{}", quote! { #b });
                if should_be_valid {
                    syn::parse((quote! {
                        sig.assert_valid_t(#title, #b_tks);
                    }).into()).unwrap()
                } else {
                    syn::parse((quote! {
                        sig.assert_invalid_t(#title, #b_tks);
                    }).into()).unwrap()
                }
            }
            SigItem::Import(path) => {
                syn::parse((quote! {
                    #path::ravencheck_exports::apply_exports(&mut sig);
                }).into()).unwrap()
                // todo!("turn import into stmt")
            }
            SigItem::Type(name, arg_len) => {
                let s = name.to_string();
                syn::parse((quote! {
                    sig.add_type_con(#s, #arg_len);
                }).into()).unwrap()
            }
            SigItem::TypeAlias(i, ty) => {
                let i_tks = format!("{}", i);
                let ty_tks = format!("{}", quote! { #ty });
                syn::parse((quote! {
                    sig.add_alias_from_string(#i_tks, #ty_tks);
                }).into()).unwrap()
            }
            SigItem::DFun(name, targs, inputs, output, body, is_rec) => {
                let name_tk: String = format!("{}", name);
                let targs: Vec<String> = targs.into_iter().map(|i| {
                    format!("{}", quote! { #i })
                }).collect();
                let body_tk: String = format!("{}", quote! {
                    |#(#inputs),*| #body
                });
                let inputs: Vec<String> = inputs.into_iter().map(|i| {
                    format!("{}", quote! { #i })
                }).collect();
                let output: String = format!("{}", quote! { #output });
                if !is_rec {
                    syn::parse((quote! {
                        sig.add_fun_tas(#name_tk, [#(#targs),*], Some(#output), #body_tk);
                    }).into()).unwrap()
                } else {
                    syn::parse((quote! {
                        sig.define_op_rec(#name_tk, [#(#targs),*], [#(#inputs),*], #output, #body_tk);
                    }).into()).unwrap()
                }
            }
            SigItem::UFun(name, targs, inputs, output) => {
                let name: String = format!("{}", name);
                let targs: Vec<String> = targs.into_iter().map(|i| {
                    format!("{}", quote! { #i })
                }).collect();
                let inputs: Vec<String> = inputs.into_iter().map(|i| {
                    format!("{}", quote! { #i })
                }).collect();
                let output: String = format!("{}", quote! { #output });
                let tokens = quote! {
                    sig.declare_op(#name, [#(#targs),*], [#(#inputs),*], #output);
                };
                // println!("{}", tokens);
                syn::parse2(tokens).unwrap()
            }
            SigItem::UConst(name, ty) => {
                let output: String = format!("{}", quote! { #ty });
                let tokens = quote! {
                    sig.declare_const(#name, #output);
                };
                syn::parse2(tokens).unwrap()
            }
        }
    }
}

#[derive(Clone)]
enum RccItem {
    DeclareType(Ident, usize),
    AttrItem(RvnAttr, Item),
}

fn extract_top_level(attrs: &mut Vec<Attribute>, rcc_items: &mut Vec<RccItem>) {
    attrs.retain_mut(|attr| {
        match &attr.meta {
            Meta::List(l) if l.path.segments.len() == 1 => {
                match l.path.segments.first().unwrap().ident.to_string().as_str() {
                    "declare_types" => {
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

                            rcc_items.push(RccItem::DeclareType(seg.ident, arity));

                            // let ident = seg.ident;
                            // let ident_str = quote!{ident}.to_string();

                            // let s: Stmt = syn::parse2(quote! {
                            //     rcc.reg_toplevel_type(#ident_str, #arity);
                            // }).unwrap();
                            // rcc_stmts.push(s);

                            // rcc_stmts.push(
                            //     SigItem::Type(seg.ident, args_len)
                            // );
                        }

                        // Don't keep
                        false
                    }

                    // Otherwise, do keep
                    _ => true,
                }
            }

            // Otherwise, do keep
            _ => true,
        }
    })
}

// #[proc_macro]
// pub fn quote_into(s: TokenStream) -> TokenStream {
//     let s: proc_macro2::TokenStream = s.into();
//     quote! {
//         syn::parse2(quote!{#s}).expect("input to quote_into should parse")
//     }.into()
// }

/// Manipulate a list of items, removing all Ravencheck-specific
/// attributes. Items are removed from the list entirely if they are
/// verification-specific.
///
/// While doing so, collect the list of attribute-item pairs that are
/// relevant to Ravencheck.
fn extract_items(items: &mut Vec<Item>, rcc_items: &mut Vec<RccItem>) {
    items.retain_mut(|item| {

        // In cases that end with 'true', the item is passed on to the
        // Rust compiler. In cases that end with 'false', the item is
        // erased.
        match extract_rvn_attr(item) {
            Some(attr) => {
                rcc_items.push(RccItem::AttrItem(attr.clone(), item.clone()));
                match &attr {
                    RvnAttr::Annotate(_) => false,
                    RvnAttr::Assume(_) => false,
                    RvnAttr::AssumeFor(_) => false,
                    RvnAttr::Declare => true,
                    RvnAttr::Define(_, is_phantom) => !is_phantom,
                    RvnAttr::Import => true,
                    RvnAttr::Verify(_) => false,
                }
            }
            None => true,
        }
    })
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum GenMode {
    Check,
    Export,
}

fn generate_stmts(items: &Vec<RccItem>, mode: GenMode) -> Vec<Stmt> {
    let mut out = Vec::new();
    for i in items {
        match i {
            RccItem::DeclareType(ident, arity) => {
                let ident_str = quote!{#ident}.to_string();
                let s: Stmt = syn::parse2(quote! {
                    rcc.reg_toplevel_type(#ident_str, #arity);
                }).unwrap();
                out.push(s);
            }
            RccItem::AttrItem(attr, item) => {
                let item_str = quote!{ #item }.to_string();
                match (attr,mode) {
                    (RvnAttr::Annotate(fname), _mode) => {
                        let s: Stmt = syn::parse2(quote! {
                            todo!("generate_stmts for Annotate");
                        }).unwrap();
                        out.push(s);
                    }
                    (RvnAttr::Assume(_rules), _) => {
                        let s: Stmt = syn::parse2(quote! {
                            rcc.reg_item_assume([], #item_str);
                        }).unwrap();
                        out.push(s);
                    }
                    (RvnAttr::AssumeFor(fname), _mode) => {
                        let s: Stmt = syn::parse2(quote! {
                            todo!("generate_stmts for AssumeFor");
                        }).unwrap();
                        out.push(s);
                    }
                    (RvnAttr::Declare, _) => {
                        let s: Stmt = syn::parse2(quote! {
                            rcc.reg_item_declare(#item_str);
                        }).unwrap();
                        out.push(s);
                    }
                    (RvnAttr::Define(_is_recursive, _is_phantom), _) => {
                        let s: Stmt = syn::parse2(quote! {
                            rcc.reg_item_define(#item_str);
                        }).unwrap();
                        out.push(s);
                    }
                    (RvnAttr::Import, _) => {
                        let s: Stmt = syn::parse2(quote! {
                            todo!("Import");
                        }).unwrap();
                        out.push(s);
                    }
                    (RvnAttr::Verify(should_be_valid), _) => {
                        let s: Stmt = syn::parse2(quote! {
                            rcc.reg_item_verify(#item_str, #should_be_valid);
                        }).unwrap();
                        out.push(s);
                    }
                    a => todo!("generate_stmts for {:?}", a)
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

    let mut rcc_items: Vec<RccItem> = Vec::new();

    // Handle commands within the top-level attributes
    extract_top_level(&mut m.attrs, &mut rcc_items);

    // Handle per-item commands within the module
    match &mut m.content {
        Some((_,items)) => {
            
            extract_items(items, &mut rcc_items);

            let test_stmts: Vec<Stmt> =
                generate_stmts(&rcc_items, GenMode::Check);

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

            println!("Here is the test module content:");
            println!("{}", test_mod);

            items.push(syn::parse(test_mod.into()).expect("parse test mod"));

            if export {
                let export_stmts: Vec<Stmt> =
                    generate_stmts(&rcc_items, GenMode::Export);

                let export_mod = quote! {
                    pub mod ravencheck_exports {
                        use #cratename::Rcc;

                        pub fn apply_exports(rcc: &mut Rcc) {
                            #(#export_stmts)*
                        }
                    }
                };

                println!("Here is the export module content:");
                println!("{}", export_mod);
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
