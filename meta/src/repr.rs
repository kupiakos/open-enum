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

use proc_macro2::{Ident, TokenStream};
use quote::ToTokens;
use syn::{parse::Parse, Error};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Repr {
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
    #[cfg(feature = "repr_c")]
    C,
}
impl Repr {
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
            #[cfg(feature = "repr_c")]
            Repr::C => "C",
        }
    }
}

impl ToTokens for Repr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend([match self {
            // Technically speaking, #[repr(C)] on an enum isn't always `c_int`,
            // but those who care can fix it if they need.
            #[cfg(feature = "repr_c")]
            Repr::C => quote::quote!(::open_enum::__private::c_int),
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
            #[cfg(feature = "repr_c")]
            "C" => Repr::C,
            #[cfg(not(feature = "repr_c"))]
            "C" => {
                return Err(Error::new(
                    ident.span(),
                    "#[repr(C)] requires either the `std` or `libc_` feature",
                ))
            }
            _ => {
                return Err(Error::new(
                    ident.span(),
                    format!("unsupported repr `{ident}`"),
                ))
            }
        })
    }
}
