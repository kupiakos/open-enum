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

use proc_macro2::Ident;
use quote::{quote, ToTokens};
use syn::{parse::Parse, Attribute, Token};

pub struct Variant {
    pub cfg_attrs: Vec<Attribute>,
    pub ident: Ident,
}

impl Parse for Variant {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            cfg_attrs: input.call(Attribute::parse_outer)?,
            ident: input.parse()?,
        })
    }
}

impl ToTokens for Variant {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let each_attr = &self.cfg_attrs;
        let ident = &self.ident;
        tokens.extend(quote! {
            #(#each_attr)*
            #ident
        });
    }
}

pub struct OpenEnumVariants {
    pub variants: Vec<Variant>,
}

impl Parse for OpenEnumVariants {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let variants = input.parse_terminated(Variant::parse, Token![,])?;

        Ok(Self {
            variants: variants.into_iter().collect(),
        })
    }
}

impl ToTokens for OpenEnumVariants {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let each_variant = &self.variants;
        tokens.extend(quote!(#(#each_variant),*));
    }
}
