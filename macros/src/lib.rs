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
    Ident,
    Item,
    ItemFn,
    ItemMod,
    Meta,
    PatType,
    Path,
    PathArguments,
    ReturnType,
    Stmt,
    Type,
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
    Assume,
    Declare,
    Define,
    Verify,
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
                    "assume" => Some(RvnAttr::Assume),
                    "declare" => Some(RvnAttr::Declare),
                    "define" => Some(RvnAttr::Define),
                    "verify" => Some(RvnAttr::Verify),
                    _ => None,
                }
            }
            Meta::List(l) if l.path.segments.len() == 1 => {
                match path_to_one_str(&l.path).as_str() {
                    "annotate" => {
                        let fun_name: Ident = l.parse_args().unwrap();
                        Some(RvnAttr::Annotate(fun_name.to_string()))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
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
    Annotation(String, Block),
    Axiom(Block),
    Goal(Block),
    TypeAlias(Ident,Type),
    DFun(Ident, Vec<PatType>, Type, Block),
    Type(Ident, usize),
    UFun(String, Vec<PatType>, Type),
}

fn handle_top_level(attrs: &mut Vec<Attribute>, sig_items: &mut Vec<SigItem>) {
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
                            let args_len = match seg.arguments {
                                PathArguments::None => 0,
                                PathArguments::AngleBracketed(a) => a.args.len(),
                                PathArguments::Parenthesized(..) => panic!("declared types should get angle-bracketed arguments <..>, but {} got parenthesized arguments", seg.ident),
                            };
                            sig_items.push(SigItem::Type(seg.ident, args_len));
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

fn handle_items(items: &mut Vec<Item>, sig_items: &mut Vec<SigItem>) {
    items.retain_mut(|item| {
        match item {
            Item::Fn(f) => {
                match pop_rvn_attr(&mut f.attrs) {
                    Some(RvnAttr::Annotate(fname)) => {
                        sig_items.push(
                            SigItem::Annotation(fname, *(f.block).clone())
                        );
                        false
                    }
                    Some(RvnAttr::Assume) => {
                        sig_items.push(
                            SigItem::Axiom(*(f.block).clone())
                        );
                        false
                    }
                    Some(RvnAttr::Declare) => {
                        let name = f.sig.ident.to_string();
                        let inputs = f.sig.inputs.iter().cloned().map(|arg| {
                            match arg {
                                FnArg::Typed(a) => a,
                                FnArg::Receiver(_) => panic!("
you can't use 'declare' on a method function (one that takes a 'self' input)"
                                ),
                            }
                        }).collect();
//                         let mut arg_types = Vec::new();
//                         for arg in f.sig.inputs.iter() {
//                             match arg {
//                                 FnArg::Typed(a) => match *(a.ty.clone()) {
//                                     Type::Path(typepath) => {
//                                         arg_types.push(
//                                             typepath.path.segments.first().unwrap().ident.to_string()
//                                         );
//                                     }
//                                     t => todo!("Handle {:?}", t),
//                                 }
//                                 FnArg::Receiver(_) => panic!("
// you can't use 'declare' on a method function (one that takes a 'self' input)"
//                                 ),
//                             }
//                         }
                        let output = match f.sig.output.clone() {
                            ReturnType::Default => panic!("
You must give a return type when using 'declare'"
                            ),
                            ReturnType::Type(_, t) => *t,
                        };
                        // let out_type = match &f.sig.output {
                        //     ReturnType::Default => "()".to_string(),
                        //     ReturnType::Type(_, t) => match *(t.clone()) {
                        //         Type::Path(typepath) => {
                        //             typepath.path.segments.first().unwrap().ident.to_string()
                        //         }
                        //         t => todo!("Handle {:?}", t),
                        //     }
                        // };
                        sig_items.push(SigItem::UFun(name, inputs, output));

                        true
                    }
                    Some(RvnAttr::Define) => {
                        let name = f.sig.ident.clone();
                        let inputs = f.sig.inputs.iter().cloned().map(|arg| {
                            match arg {
                                FnArg::Typed(a) => a,
                                FnArg::Receiver(_) => panic!("
you can't use 'define' on a method function (one that takes a 'self' input)"
                                ),
                            }
                        }).collect();
                        let output = match f.sig.output.clone() {
                            ReturnType::Default => panic!("
You must give a return type when using 'define'"
                            ),
                            ReturnType::Type(_, t) => *t,
                        };
                        let body = (*f.block).clone();

                        sig_items.push(
                            SigItem::DFun(name, inputs, output, body)
                        );
                        true
                    }
                    Some(RvnAttr::Verify) => {
                        sig_items.push(
                            SigItem::Goal(*(f.block).clone())
                        );
                        false
                    }
                    _ => true,
                }
            }
            Item::Const(i) => {
                match pop_rvn_attr(&mut i.attrs) {
                    _ => true,
                }
            }
            Item::Struct(i) => {
                match pop_rvn_attr(&mut i.attrs) {
                    Some(RvnAttr::Declare) => {
                        sig_items.push(SigItem::Type(i.ident.clone(), 0));
                    }
                    Some(a) => panic!(
                        "attr {:?} cannot not be used on a struct definition",
                        a,
                    ),
                    None => {}
                }
                true
            }
            Item::Type(i) => {
                match pop_rvn_attr(&mut i.attrs) {
                    Some(RvnAttr::Declare) => {
                        sig_items.push(SigItem::Type(i.ident.clone(), 0));
                    }
                    Some(RvnAttr::Define) => {
                        sig_items.push(SigItem::TypeAlias(
                            i.ident.clone(),
                            *(i.ty).clone(),
                        ));
                    }
                    Some(a) => panic!(
                        "attr {:?} cannot not be used on a type alias definition",
                        a,
                    ),
                    None => {}
                }
                true
            }
            _ => true,
        }
    });
}

#[proc_macro_attribute]
pub fn check_module(attrs: TokenStream, input: TokenStream) -> TokenStream {

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

    let mut sig_items: Vec<SigItem> = Vec::new();

    // Handle commands within the top-level attributes
    handle_top_level(&mut m.attrs, &mut sig_items);

    // Handle per-item commands within the module
    match &mut m.content {
        Some((_,items)) => {
            handle_items(items, &mut sig_items);

            // Turn sig_items into statements (of type syn::Stmt)
            let stmts: Vec<Stmt> = sig_items.into_iter().map(|i| {
                match i {
                    SigItem::Annotation(f,b) => {
                        let b_tks = format!("{}", quote! { #b });
                        syn::parse((quote! {
                            sig.add_annotation(#f, #b_tks);
                        }).into()).unwrap()
                    }
                    SigItem::Axiom(b) => {
                        let b_tks = format!("{}", quote! { #b });
                        syn::parse((quote! {
                            sig.add_axiom(#b_tks);
                        }).into()).unwrap()
                    }
                    SigItem::Goal(b) => {
                        let b_tks = format!("{}", quote! { #b });
                        syn::parse((quote! {
                            sig.assert_valid(#b_tks);
                        }).into()).unwrap()
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
                    SigItem::DFun(name, inputs, _output, body) => {
                        let name_tk: String = format!("{}", name);
                        let body_tk: String = format!("{}", quote! {
                            |#(#inputs),*| #body
                        });
                        syn::parse((quote! {
                            sig.add_fun(#name_tk, #body_tk);
                        }).into()).unwrap()
                    }
                    SigItem::UFun(name, inputs, output) => {
                        let name: String = format!("{}", name);
                        let inputs: Vec<String> = inputs.into_iter().map(|i| {
                            format!("{}", quote! { #i })
                        }).collect();
                        let output: String = format!("{}", quote! { #output });
                        let tokens = quote! {
                            sig.declare_op(#name, [#(#inputs),*], #output);
                        };
                        syn::parse2(tokens).unwrap()
                        // let i_tks_v: Vec<String> = inputs.into_iter().map(|i| {
                        //     format!("{}", i)
                        // }).collect();
                        // let tks = if output.to_string() == "bool" {
                        //     quote! {
                        //         sig.add_relation(#name, [#(#i_tks_v),*]);
                        //     }
                        // } else {
                        //     let o_tks = format!("{}", output);
                        //     quote! {
                        //         sig.declare_op(#name, [#(#i_tks_v),*], #o_tks);
                        //     }
                        // };
                        // syn::parse(tks.into()).unwrap()
                    }
                }
            }).collect();
            let test: ItemFn = syn::parse((quote! {
                #[test]
                fn check_properties() {
                    let mut sig = CheckedSig::empty();

                    // Interpolate 'stmts' here
                    #(#stmts)*
                }
            }).into()).unwrap();

            let test_s = Item::Fn(test);

            let test_mod = quote! {
                #[cfg(test)]
                mod ravencheck_tests {
                    use #cratename::CheckedSig;

                    #test_s
                }
            };

            items.push(syn::parse(test_mod.into()).expect("parse test mod"));
        }
        None => {}
    }
    let out = quote! {
        #m
    };
    out.into()
}
