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

use core::ops::RangeInclusive;
use proc_macro2::{Literal, Span, TokenStream};
use quote::{quote, ToTokens};
use std::collections::HashSet;
use syn::{
    parse::Parse, parse_macro_input, punctuated::Punctuated, spanned::Spanned, Error, Expr, Ident,
    ItemEnum, Path, Token,
};

#[derive(Clone)]
enum Discriminant {
    Literal(i128),
    Nonliteral { base: Expr, offset: u32 },
}

impl Discriminant {
    fn new(discriminant_expr: Expr) -> syn::Result<Self> {
        // Positive literal int
        if let syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) = &discriminant_expr
        {
            return Ok(Discriminant::Literal(lit.base10_parse()?));
        }

        // Negative literal int
        if let syn::Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Neg(_),
            expr,
            ..
        }) = &discriminant_expr
        {
            if let syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(lit),
                ..
            }) = &**expr
            {
                return Ok(Discriminant::Literal(-lit.base10_parse()?));
            }
        }

        // Nonliteral expression
        Ok(Discriminant::Nonliteral {
            base: discriminant_expr,
            offset: 0,
        })
    }

    fn next_value(self) -> Option<Self> {
        Some(match self {
            Discriminant::Literal(val) => Discriminant::Literal(val.checked_add(1)?),
            Discriminant::Nonliteral { base, offset } => Discriminant::Nonliteral {
                base,
                offset: offset.checked_add(1)?,
            },
        })
    }
}

impl ToTokens for Discriminant {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match self {
            Discriminant::Literal(value) => Literal::i128_unsuffixed(*value).into_token_stream(),
            Discriminant::Nonliteral { base, offset } => {
                if *offset == 0 {
                    base.into_token_stream()
                } else {
                    let offset = Literal::u32_unsuffixed(*offset);
                    quote!(#base + #offset)
                }
            }
        })
    }
}

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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Repr {
    I8,
    U8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    Usize,
    Isize,
    C,
}

fn range_contains(x: &RangeInclusive<i128>, y: &RangeInclusive<i128>) -> bool {
    x.contains(y.start()) && x.contains(y.end())
}

impl Repr {
    const REPR_RANGES: &'static [(Repr, RangeInclusive<i128>)] = &[
        (Repr::I8, (i8::MIN as i128)..=(i8::MAX as i128)),
        (Repr::U8, (u8::MIN as i128)..=(u8::MAX as i128)),
        (Repr::I16, (i16::MIN as i128)..=(i16::MAX as i128)),
        (Repr::U16, (u16::MIN as i128)..=(u16::MAX as i128)),
        (Repr::I32, (i32::MIN as i128)..=(i32::MAX as i128)),
        (Repr::U32, (u32::MIN as i128)..=(u32::MAX as i128)),
        (Repr::I64, (i64::MIN as i128)..=(i64::MAX as i128)),
        (Repr::U64, (u64::MIN as i128)..=(u64::MAX as i128)),
        (Repr::Isize, (isize::MIN as i128)..=(isize::MAX as i128)),
        (Repr::Usize, (usize::MIN as i128)..=(usize::MAX as i128)),
    ];

    /// Finds the smallest repr that can fit this range, if any.
    fn smallest_fitting_repr(range: RangeInclusive<i128>) -> Option<Self> {
        // TODO: perhaps check this logic matches current rustc behavior?
        for (repr, repr_range) in Self::REPR_RANGES {
            if range_contains(repr_range, &range) {
                return Some(*repr);
            }
        }
        None
    }

    fn name(self) -> &'static str {
        match self {
            Repr::I8 => "i8",
            Repr::U8 => "u8",
            Repr::U16 => "u16",
            Repr::I16 => "i16",
            Repr::U32 => "u32",
            Repr::I32 => "i32",
            Repr::U64 => "u64",
            Repr::I64 => "i64",
            Repr::Usize => "usize",
            Repr::Isize => "isize",
            Repr::C => "C",
        }
    }
}

impl ToTokens for Repr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend([match self {
            // Technically speaking, #[repr(C)] on an enum isn't always `c_int`,
            // but those who care can fix it if they need.
            Repr::C => quote!(::open_enum::__private::c_int),
            x => x.name().parse::<TokenStream>().unwrap(),
        }])
    }
}

impl Parse for Repr {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let ident: Ident = input.parse()?;
        Ok(match ident.to_string().as_str() {
            "i8" => Repr::I8,
            "u8" => Repr::U8,
            "i16" => Repr::I16,
            "u16" => Repr::U16,
            "i32" => Repr::I32,
            "u32" => Repr::U32,
            "i64" => Repr::I64,
            "u64" => Repr::U64,
            "usize" => Repr::Usize,
            "isize" => Repr::Isize,
            "C" => Repr::C,
            _ => {
                return Err(Error::new(
                    ident.span(),
                    format!("unsupported repr `{ident}`"),
                ))
            }
        })
    }
}

/// Figure out what the internal representation of the enum should be given its variants.
///
/// If we don't have sufficient info to auto-shrink the internal repr, fallback to isize.
fn autodetect_inner_repr<'a>(variants: impl Iterator<Item = &'a Discriminant>) -> Repr {
    let mut variants = variants.peekable();
    if variants.peek().is_none() {
        // TODO: maybe use the unit type for a fieldless open enum without a #[repr]?
        return Repr::Isize;
    }
    let mut min = i128::MAX;
    let mut max = i128::MIN;
    for value in variants {
        match value {
            &Discriminant::Literal(value) => {
                min = min.min(value);
                max = max.max(value);
            }
            Discriminant::Nonliteral { .. } => {
                // No way to do fancy sizing here, fall back to isize.
                return Repr::Isize;
            }
        }
    }
    Repr::smallest_fitting_repr(min..=max).unwrap_or(Repr::Isize)
}

/// Checks that there are no duplicate discriminant values. If all variants are literals, return an `Err` so we can have
/// more clear error messages. Otherwise, emit a static check that ensures no duplicates.
fn check_no_alias<'a>(
    name: &Ident,
    repr: Repr,
    variants: impl Iterator<Item = (&'a Ident, &'a Discriminant, Span)> + Clone,
) -> syn::Result<TokenStream> {
    let variant_idents = variants.clone().map(|x| x.0);

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
            return Ok(check_no_alias_nonliteral(name, repr, variant_idents));
        }
    }
    Ok(TokenStream::default())
}

fn check_no_alias_nonliteral<'a>(
    name: &Ident,
    repr: Repr,
    variants: impl Iterator<Item = &'a Ident>,
) -> TokenStream {
    let test_fn = Ident::new(&format!("no_duplicates_{}", repr.name()), Span::call_site());
    quote!(
        const _: () = assert!(open_enum::__private:: #test_fn ([ #( #name::#variants .0 ),* ]), "discriminant value assigned more than once");
    )
}

fn is_lint_attribute(attr: &syn::Attribute) -> bool {
    ["allow", "warn", "deny", "forbid"]
        .into_iter()
        .any(|s| attr.path.is_ident(s))
}

fn open_enum_impl(mut enum_: ItemEnum, allow_alias: bool) -> Result<TokenStream, Error> {
    // Does the enum define a `#[repr()]`?
    let mut explicit_repr: Option<Repr> = None;

    {
        let mut err = Ok(());
        enum_.attrs.retain(|attr| {
            if attr.path.is_ident("repr") {
                match attr.parse_args() {
                    Ok(repr) => explicit_repr = Some(repr),
                    Err(e) => err = Err(e),
                }
                false
            } else if attr.path.is_ident("non_exhaustive") {
                // technically it's exhaustive if the enum covers the full integer range
                err = Err(Error::new(attr.path.span(), "`non_exhaustive` cannot be applied to an open enum; it is already non-exhaustive"));
                false
            } else {
                true
            }
        });
        err?;
    }

    if !enum_.generics.params.is_empty() {
        return Err(Error::new(enum_.generics.span(), "enum cannot be generic"));
    }

    let mut variants = Vec::with_capacity(enum_.variants.len());
    let mut last_field = Discriminant::Literal(-1);
    for variant in enum_.variants {
        if !matches!(variant.fields, syn::Fields::Unit) {
            return Err(Error::new(variant.span(), "enum cannot contain fields"));
        }

        let (value, value_span) = if let Some((_, discriminant)) = variant.discriminant {
            let span = discriminant.span();
            (Discriminant::new(discriminant)?, span)
        } else {
            last_field = last_field
                .next_value()
                .ok_or_else(|| Error::new(variant.span(), "enum discriminant overflowed"))?;
            (last_field.clone(), variant.ident.span())
        };
        last_field = value.clone();
        variants.push((variant.ident, value, value_span, variant.attrs))
    }
    // The proper repr to type-check against
    let typecheck_repr: Repr = explicit_repr.unwrap_or(Repr::Isize);

    let syn::ItemEnum {
        ident, vis, attrs, ..
    } = enum_;

    let mut impl_attrs: Vec<TokenStream> = vec![quote!(#[allow(non_upper_case_globals)])];

    // To make `match` seamless, derive(PartialEq, Eq) if they aren't already.
    let mut our_derives = HashSet::new();
    our_derives.insert("PartialEq");
    our_derives.insert("Eq");
    for attr in &attrs {
        if attr.path.is_ident("derive") {
            let derives = attr.parse_args_with(Punctuated::<Path, Token![,]>::parse_terminated)?;
            for derive in derives {
                if derive.is_ident("PartialEq") {
                    our_derives.remove("PartialEq");
                } else if derive.is_ident("Eq") {
                    our_derives.remove("Eq");
                }
            }
        } else if is_lint_attribute(attr) {
            impl_attrs.push(attr.to_token_stream());
        }
    }

    // Convert to a token stream to not unnecessarily parse more.
    let mut struct_attrs: Vec<TokenStream> = attrs
        .into_iter()
        .map(syn::Attribute::into_token_stream)
        .collect();

    // The actual representation of the value.
    let inner_repr = if let Some(explicit_repr) = explicit_repr {
        // If there is an explicit repr, emit #[repr(transparent)].
        struct_attrs.push(quote!(#[repr(transparent)]));
        explicit_repr
    } else {
        // If there isn't an explicit repr, determine an appropriate sized integer that will fit.
        // Interpret all discriminant expressions as isize.
        autodetect_inner_repr(variants.iter().map(|v| &v.1))
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
        check_no_alias(
            &ident,
            inner_repr,
            variants.iter().map(|(i, v, s, _)| (i, v, *s)),
        )?
    };

    let fields = variants.into_iter()
        .map(|(name, value, value_span, attrs)| {
            let mut value = value.into_token_stream();
            value = set_token_stream_span(value, value_span);
            quote!(
                #(#attrs)*
                pub const #name: Self = Self(::core::convert::identity::<#typecheck_repr>(#value) as #inner_repr);
            )
        });

    Ok(quote! {
        #(#struct_attrs)*
        #vis struct #ident(pub #inner_repr);

        #(#impl_attrs)*
        impl #ident {
            #(
                #fields
            )*
        }
        #alias_check
    })
}

/// Constructs an *open* enum from a Rust enum definition.
///
/// See the module documentation for more details.
#[proc_macro_attribute]
pub fn open_enum(
    attrs: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let enum_ = parse_macro_input!(input as syn::ItemEnum);
    let attrs = parse_macro_input!(attrs with Punctuated::<Path, Token![,]>::parse_terminated);
    let mut allow_alias = false;
    for attr in attrs {
        if attr.is_ident("allow_alias") {
            allow_alias = true;
        } else {
            return Error::new(
                attr.span(),
                &format!(
                    "{attr} is not a recognized open_enum option",
                    attr = attr.into_token_stream().to_string()
                ),
            )
            .into_compile_error()
            .into();
        }
    }

    open_enum_impl(enum_, allow_alias)
        .unwrap_or_else(Error::into_compile_error)
        .into()
}
