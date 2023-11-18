// Copyright © 2023 Microsoft Corporation
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

extern crate open_enum;
use open_enum::*;

#[open_enum]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, zerocopy::AsBytes, zerocopy::FromBytes, zerocopy::FromZeroes,
)]
#[repr(u32)]
pub enum Color {
    Red = 1,
    Blue = 2,
}

#[open_enum]
#[derive(
    core::fmt::Debug,
    std::clone::Clone,
    ::core::marker::Copy,
    std::cmp::PartialEq,
    ::core::cmp::Eq,
    zerocopy::AsBytes,
    ::zerocopy::FromBytes,
    zerocopy::FromZeroes,
)]
#[repr(u32)]
pub enum ColorWithNonPreludeDerives {
    Red = 1,
    Blue = 2,
}

// Ensure that `Color` actually implements the `derive`d traits.
#[derive(
    Debug, Copy, Clone, PartialEq, Eq, zerocopy::AsBytes, zerocopy::FromBytes, zerocopy::FromZeroes,
)]
#[repr(C)]
pub struct EmbedColor {
    pub color: Color,
}

#[derive(
    Debug, Copy, Clone, PartialEq, Eq, zerocopy::AsBytes, zerocopy::FromBytes, zerocopy::FromZeroes,
)]
#[repr(C)]
pub struct EmbedColorWithNonPreludeDerives {
    pub color: ColorWithNonPreludeDerives,
}

#[test]
fn embedded_enum_struct_partialeq() {
    assert_eq!(
        EmbedColor { color: Color::Red },
        EmbedColor { color: Color::Red }
    );
    assert_ne!(
        EmbedColor { color: Color::Red },
        EmbedColor { color: Color::Blue }
    );
}

#[test]
fn embedded_enum_struct_debug() {
    let debug_str = format!("{:?}", EmbedColor { color: Color::Red });
    assert!(debug_str.contains("Red"), "{debug_str}");
}

#[test]
fn extended_embedded_enum_struct_debug() {
    let debug_str = format!(
        "{:?}",
        EmbedColorWithNonPreludeDerives {
            color: ColorWithNonPreludeDerives::Red
        }
    );
    assert!(debug_str.contains("Red"), "{debug_str}");
}
