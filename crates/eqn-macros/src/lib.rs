//! Derive macros for `eqn-core` traits. Generated code names traits via
//! `::eqn_core::...`, so `eqn_core` re-exports these instead of the other
//! way around.

use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, Expr, Path, Type, parse_macro_input, parse_quote};

/// Emits `impl <trait> for <ty> {}` for a marker trait, preserving generics.
fn marker_impl(input: TokenStream, trait_path: Path) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    quote! {
        impl #impl_generics #trait_path for #name #ty_generics #where_clause {}
    }
    .into()
}

/// Declares the operator associative. Requires a `BinaryOperator` impl.
#[proc_macro_derive(Associative)]
pub fn derive_associative(input: TokenStream) -> TokenStream {
    marker_impl(input, parse_quote!(::eqn_core::op::Associative))
}

/// Declares the operator commutative. Requires a `BinaryOperator` impl.
#[proc_macro_derive(Commutative)]
pub fn derive_commutative(input: TokenStream) -> TokenStream {
    marker_impl(input, parse_quote!(::eqn_core::op::Commutative))
}

/// `#[derive(Set)] #[set(element = T)] struct S;` emits `impl Set for S { type
/// Element = T; }`.
#[proc_macro_derive(Set, attributes(set))]
pub fn derive_set(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let element = match set_element(&input) {
        Ok(ty) => ty,
        Err(e) => return e.to_compile_error().into(),
    };
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    quote! {
        impl #impl_generics ::eqn_core::set::Set for #name #ty_generics #where_clause {
            type Element = #element;
        }
    }
    .into()
}

fn set_element(input: &DeriveInput) -> syn::Result<Type> {
    let attr = input
        .attrs
        .iter()
        .find(|a| a.path().is_ident("set"))
        .ok_or_else(|| syn::Error::new_spanned(&input.ident, "missing `#[set(element = T)]`"))?;
    let mut element = None;
    attr.parse_nested_meta(|meta| {
        if meta.path.is_ident("element") {
            element = Some(meta.value()?.parse::<Type>()?);
            Ok(())
        } else {
            Err(meta.error("expected `element = T`"))
        }
    })?;
    element.ok_or_else(|| syn::Error::new_spanned(attr, "missing `element = T`"))
}

/// ```ignore
/// #[derive(BinaryOperator)]
/// #[operator(domain = Ints, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
/// struct Add;
/// ```
/// `identity` and `inverse` are optional and add `Identity` / `Inverse` impls.
#[proc_macro_derive(BinaryOperator, attributes(operator))]
pub fn derive_binary_operator(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let op = match Operator::parse(&input) {
        Ok(op) => op,
        Err(e) => return e.to_compile_error().into(),
    };
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let Operator {
        domain,
        apply,
        identity,
        inverse,
    } = op;
    let elem = quote!(<#domain as ::eqn_core::set::Set>::Element);

    let identity = identity.map(|id| {
        quote! {
            impl #impl_generics ::eqn_core::op::Identity for #name #ty_generics #where_clause {
                const IDENTITY: #elem = #id;
            }
        }
    });
    let inverse = inverse.map(|inv| {
        quote! {
            impl #impl_generics ::eqn_core::op::Inverse for #name #ty_generics #where_clause {
                fn inverse(a: #elem) -> #elem {
                    let f: fn(#elem) -> #elem = #inv;
                    f(a)
                }
            }
        }
    });
    quote! {
        impl #impl_generics ::eqn_core::op::BinaryOperator for #name #ty_generics #where_clause {
            type Domain = #domain;
            fn apply(a: #elem, b: #elem) -> #elem {
                let f: fn(#elem, #elem) -> #elem = #apply;
                f(a, b)
            }
        }
        #identity
        #inverse
    }
    .into()
}

struct Operator {
    domain: Type,
    apply: Expr,
    identity: Option<Expr>,
    inverse: Option<Expr>,
}

impl Operator {
    fn parse(input: &DeriveInput) -> syn::Result<Self> {
        let attr = input
            .attrs
            .iter()
            .find(|a| a.path().is_ident("operator"))
            .ok_or_else(|| {
                syn::Error::new_spanned(
                    &input.ident,
                    "missing `#[operator(domain = D, apply = ...)]`",
                )
            })?;
        let (mut domain, mut apply, mut identity, mut inverse) = (None, None, None, None);
        attr.parse_nested_meta(|meta| {
            let value = meta.value()?;
            if meta.path.is_ident("domain") {
                domain = Some(value.parse()?);
            } else if meta.path.is_ident("apply") {
                apply = Some(value.parse()?);
            } else if meta.path.is_ident("identity") {
                identity = Some(value.parse()?);
            } else if meta.path.is_ident("inverse") {
                inverse = Some(value.parse()?);
            } else {
                return Err(meta.error("expected `domain`, `apply`, `identity` or `inverse`"));
            }
            Ok(())
        })?;
        Ok(Self {
            domain: domain.ok_or_else(|| syn::Error::new_spanned(attr, "missing `domain = D`"))?,
            apply: apply
                .ok_or_else(|| syn::Error::new_spanned(attr, "missing `apply = |a, b| ...`"))?,
            identity,
            inverse,
        })
    }
}
