// Copyright 2022 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

extern crate proc_macro;

mod config;
mod discriminant;
mod repr;

use config::Config;

use discriminant::Discriminant;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use repr::Repr;
use std::collections::HashSet;
use syn::{
    parse_macro_input, punctuated::Punctuated, spanned::Spanned, Error, Ident, ItemEnum, Path,
    Token, Visibility,
};

/// Sets the span for every token tree in the token stream
fn set_token_stream_span(tokens: TokenStream, span: Span) -> TokenStream {
    tokens
        .into_iter()
        .map(|mut tt| {
            tt.set_span(span);
            tt
        })
        .collect()
}

/// Checks that there are no duplicate discriminant values. If all variants are literals, return an `Err` so we can have
/// more clear error messages. Otherwise, emit a static check that ensures no duplicates.
fn check_no_alias<'a>(
    enum_: &ItemEnum,
    variants: impl Iterator<Item = (&'a Ident, &'a Discriminant, Span)> + Clone,
) -> syn::Result<TokenStream> {
    // If they're all literals, we can give better error messages by checking at proc macro time.
    let mut values: HashSet<i128> = HashSet::new();
    for (_, variant, span) in variants {
        if let &Discriminant::Literal(value) = variant {
            if !values.insert(value) {
                return Err(Error::new(
                    span,
                    &format!("discriminant value `{value}` assigned more than once"),
                ));
            }
        } else {
            let mut checking_enum = syn::ItemEnum {
                ident: format_ident!("_Check{}", enum_.ident),
                vis: Visibility::Inherited,
                ..enum_.clone()
            };
            checking_enum.attrs.retain(|attr| {
                matches!(
                    attr.path.to_token_stream().to_string().as_str(),
                    "repr" | "allow" | "warn" | "deny" | "forbid"
                )
            });
            return Ok(quote!(
                #[allow(dead_code)]
                #checking_enum
            ));
        }
    }
    Ok(TokenStream::default())
}

fn open_enum_impl(
    enum_: ItemEnum,
    Config {
        allow_alias,
        repr_visibility,
        primitive_conversions,
    }: Config,
) -> Result<TokenStream, Error> {
    // Does the enum define a `#[repr()]`?
    let mut struct_attrs: Vec<TokenStream> = Vec::with_capacity(enum_.attrs.len() + 5);
    struct_attrs.push(quote!(#[allow(clippy::exhaustive_structs)]));

    if !enum_.generics.params.is_empty() {
        return Err(Error::new(enum_.generics.span(), "enum cannot be generic"));
    }
    let mut variants = Vec::with_capacity(enum_.variants.len());
    let mut last_field = Discriminant::Literal(-1);
    for variant in &enum_.variants {
        if !matches!(variant.fields, syn::Fields::Unit) {
            return Err(Error::new(variant.span(), "enum cannot contain fields"));
        }

        let (value, value_span) = if let Some((_, discriminant)) = &variant.discriminant {
            let span = discriminant.span();
            (Discriminant::new(discriminant.clone())?, span)
        } else {
            last_field = last_field
                .next_value()
                .ok_or_else(|| Error::new(variant.span(), "enum discriminant overflowed"))?;
            (last_field.clone(), variant.ident.span())
        };
        last_field = value.clone();
        variants.push((&variant.ident, value, value_span, &variant.attrs))
    }

    let mut impl_attrs: Vec<TokenStream> = vec![quote!(#[allow(non_upper_case_globals)])];
    let mut explicit_repr: Option<Repr> = None;

    // To make `match` seamless, derive(PartialEq, Eq) if they aren't already.
    let mut our_derives = HashSet::new();
    our_derives.insert("PartialEq");
    our_derives.insert("Eq");
    for attr in &enum_.attrs {
        let mut include_in_struct = true;
        // Turns out `is_ident` does a `to_string` every time
        match attr.path.to_token_stream().to_string().as_str() {
            "derive" => {
                let derives =
                    attr.parse_args_with(Punctuated::<Path, Token![,]>::parse_terminated)?;
                for derive in derives {
                    if derive.is_ident("PartialEq") {
                        our_derives.remove("PartialEq");
                    } else if derive.is_ident("Eq") {
                        our_derives.remove("Eq");
                    }
                }
            }
            // Copy linting attribute to the impl.
            "allow" | "warn" | "deny" | "forbid" => impl_attrs.push(attr.to_token_stream()),
            "repr" => {
                assert!(explicit_repr.is_none(), "duplicate explicit repr");
                explicit_repr = Some(attr.parse_args()?);
                include_in_struct = false;
            }
            "non_exhaustive" => {
                // technically it's exhaustive if the enum covers the full integer range
                return Err(Error::new(attr.path.span(), "`non_exhaustive` cannot be applied to an open enum; it is already non-exhaustive"));
            }
            _ => {}
        }
        if include_in_struct {
            struct_attrs.push(attr.to_token_stream());
        }
    }

    // The proper repr to type-check against
    let typecheck_repr: Repr = explicit_repr.unwrap_or(Repr::Isize);

    // The actual representation of the value.
    let inner_repr = match explicit_repr {
        Some(explicit_repr) => {
            // If there is an explicit repr, emit #[repr(transparent)].
            struct_attrs.push(quote!(#[repr(transparent)]));
            explicit_repr
        }
        None => {
            // If there isn't an explicit repr, determine an appropriate sized integer that will fit.
            // Interpret all discriminant expressions as isize.
            repr::autodetect_inner_repr(variants.iter().map(|v| &v.1))
        }
    };

    if !our_derives.is_empty() {
        let our_derives = our_derives
            .into_iter()
            .map(|d| Ident::new(d, Span::call_site()));
        struct_attrs.push(quote!(#[derive(#(#our_derives),*)]));
    }

    let alias_check = if allow_alias {
        TokenStream::default()
    } else {
        check_no_alias(&enum_, variants.iter().map(|(i, v, s, _)| (*i, v, *s)))?
    };

    let syn::ItemEnum { ident, vis, .. } = enum_;

    let fields = variants
        .into_iter()
        .map(|(name, value, value_span, attrs)| {
            let mut value = value.into_token_stream();
            value = set_token_stream_span(value, value_span);
            let inner = if typecheck_repr == inner_repr {
                value
            } else {
                quote!(::core::convert::identity::<#typecheck_repr>(#value) as #inner_repr)
            };
            quote!(
                #(#attrs)*
                pub const #name: #ident = #ident(#inner);
            )
        });

    let try_froms = if primitive_conversions {
        let primitives = [
            Repr::I8,
            Repr::U8,
            Repr::U16,
            Repr::I16,
            Repr::U32,
            Repr::I32,
            Repr::U64,
            Repr::I64,
            Repr::Usize,
            Repr::Isize,
        ];
        TokenStream::from_iter(
            primitives
                .iter()
                .filter(|&repr| {
                    // Skip our own inner_repr because core implements TryFrom based
                    // on the existence of an infallible From implementation.
                    *repr != inner_repr
                })
                .map(|prim| {
                    quote! {
                        impl std::convert::TryFrom<#prim> for #ident {
                            type Error = <#inner_repr as TryFrom<#prim>>::Error;
                            fn try_from(val: #prim) -> Result<Self, Self::Error> {
                                let val = #inner_repr::try_from(val)?;
                                Ok(Self(val))
                            }
                        }

                        impl std::convert::TryFrom<#ident> for #prim {
                            type Error = <#prim as TryFrom<#inner_repr>>::Error;
                            fn try_from(val: #ident) -> Result<Self, Self::Error> {
                                let val = #prim::try_from(val.0)?;
                                Ok(val)
                            }
                        }
                    }
                }),
        )
    } else {
        TokenStream::default()
    };

    Ok(quote! {
        #(#struct_attrs)*
        #vis struct #ident(#repr_visibility #inner_repr);

        #(#impl_attrs)*
        impl #ident {
            #(
                #fields
            )*
        }
        #alias_check

        impl From<#inner_repr> for #ident {
            fn from(val: #inner_repr) -> Self {
                Self(val)
            }
        }

        impl From<#ident> for #inner_repr {
            fn from(val: #ident) -> Self {
                val.0
            }
        }
        #try_froms

    })
}

#[proc_macro_attribute]
pub fn open_enum(
    attrs: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let enum_ = parse_macro_input!(input as syn::ItemEnum);
    let config = parse_macro_input!(attrs as Config);
    open_enum_impl(enum_, config)
        .unwrap_or_else(Error::into_compile_error)
        .into()
}
