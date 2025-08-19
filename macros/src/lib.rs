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
    ReturnType,
    Stmt,
    Type,
};


#[proc_macro]
pub fn verify(input: TokenStream) -> TokenStream {
    // let args: Punctuated<syn::Expr,syn::token::Comma> = syn::parse(input).unwrap();
    let mut args: Vec<syn::Expr> = syn::parse_macro_input!(input with Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated).into_iter().collect();
    let e = args.pop().unwrap();
    let sig = args.pop().unwrap();
    let out = quote! {
        (#sig).assert_valid(stringify!(#e));
    };
    // println!("{}", out);
    out.into()
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RvnAttr {
    Annotate(String),
    Assume,
    Declare,
    Verify,
}

fn pop_rvn_attr(attrs: &mut Vec<Attribute>) -> Option<RvnAttr> {
    let mut out = None;
    attrs.retain_mut(|attr| {
        match &attr.meta {
            Meta::Path(p) if p.segments.len() == 1 => {
                match p.segments.first().unwrap().ident.to_string().as_str() {
                    "assume" => {
                        assert!(
                            out == None,
                            "only one attr should be used per item, but used both {:?} and another",
                            out.clone().unwrap(),
                        );
                        out = Some(RvnAttr::Assume);
                        false
                    }
                    "declare" => {
                        assert!(
                            out == None,
                            "only one attr should be used per item, but used both {:?} and another",
                            out.clone().unwrap(),
                        );
                        out = Some(RvnAttr::Declare);
                        false
                    }
                    "verify" => {
                        assert!(
                            out == None,
                            "only one attr should be used per item, but used both {:?} and another",
                            out.clone().unwrap(),
                        );
                        out = Some(RvnAttr::Verify);
                        false
                    }
                    _ => true,
                }
            }
            Meta::List(l) if l.path.segments.len() == 1 => {
                match l.path.segments.first().unwrap().ident.to_string().as_str() {
                    "annotate" => {
                        out = Some(RvnAttr::Annotate(String::new()));
                        false
                    }
                    _ => true,
                }
            }
            _ => true,
        }
    });

    out
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SigItem {
    // Annotation(String, String),
    Axiom(Block),
    Goal(Block),
    Sort(String),
    UFun(String, Vec<String>, String),
}

fn handle_top_level(attrs: &mut Vec<Attribute>, sig_items: &mut Vec<SigItem>) {
    attrs.retain_mut(|attr| {
        match &attr.meta {
            Meta::List(l) if l.path.segments.len() == 1 => {
                match l.path.segments.first().unwrap().ident.to_string().as_str() {
                    "declare_types" => {
                        // parse out the type name arg, then push to sig_items
                        // let types: Ident = l.parse_args().unwrap();
                        // let types: Punctuated<Ident,Token![,]> = Punctuated::parse_terminated(l.tokens).unwrap();

                        let parser =
                            Punctuated
                            ::<Ident,syn::Token![,]>
                            ::parse_separated_nonempty;
                        let types = parser
                            .parse2(l.tokens.clone())
                            .expect("the #[declare_types(..)] attribute expects one or more type names as arguments");

                        for t in types.iter() {
                            sig_items.push(SigItem::Sort(t.to_string()));
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
                    Some(RvnAttr::Annotate(_)) => false,
                    Some(RvnAttr::Assume) => {
                        sig_items.push(
                            SigItem::Axiom(*(f.block).clone())
                        );
                        false
                    }
                    Some(RvnAttr::Declare) => {
                        let name = f.sig.ident.to_string();
                        let mut arg_types = Vec::new();
                        for arg in f.sig.inputs.iter() {
                            match arg {
                                FnArg::Typed(a) => match *(a.ty.clone()) {
                                    Type::Path(typepath) => {
                                        arg_types.push(
                                            typepath.path.segments.first().unwrap().ident.to_string()
                                        );
                                    }
                                    t => todo!("Handle {:?}", t),
                                }
                                // FnArg::Typed(_p) => {
                                //     arg_types.push(
                                //         stringify!(_p.ty).to_string()
                                //     );
                                // }
                                FnArg::Receiver(_) => panic!("
you can't use 'declare' on a method function (one that takes a 'self' input)"
                                ),
                            }
                        }
                        let out_type = match &f.sig.output {
                            ReturnType::Default => "()".to_string(),
                            ReturnType::Type(_, t) => match *(t.clone()) {
                                Type::Path(typepath) => {
                                    typepath.path.segments.first().unwrap().ident.to_string()
                                }
                                t => todo!("Handle {:?}", t),
                            }
                        };
                        sig_items.push(SigItem::UFun(name, arg_types, out_type));

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
                        sig_items.push(SigItem::Sort(i.ident.to_string()));
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
                        sig_items.push(SigItem::Sort(i.ident.to_string()));
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
                    SigItem::Sort(s) => {
                        syn::parse((quote! {
                            sig.add_sort(#s);
                        }).into()).unwrap()
                    }
                    SigItem::UFun(name, inputs, output) => {
                        let i_tks_v: Vec<String> = inputs.into_iter().map(|i| {
                            format!("{}", i)
                        }).collect();
                        let tks = if output.as_str() == "bool" {
                            quote! {
                                sig.add_relation(#name, [#(#i_tks_v),*]);
                            }
                        } else {
                            let o_tks = format!("{}", output);
                            quote! {
                                sig.declare_op(#name, [#(#i_tks_v),*], #o_tks);
                            }
                        };
                        syn::parse(tks.into()).unwrap()
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
