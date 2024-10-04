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
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    ToRepr,
    FromRepr,
    zerocopy::AsBytes,
    zerocopy::FromBytes,
    zerocopy::FromZeroes,
)]
#[repr(u32)]
pub enum Color {
    Red = 1,
    Blue = 2,
}

#[open_enum]
#[derive(Debug, Clone, Copy, PartialEq, Eq, ToRepr, TryFromKnownRepr)]
#[repr(u32)]
pub enum ColorWithFeatures {
    Red = 1,
    Blue = 2,
    /// Test doc
    #[cfg(feature = "std")]
    Orange = 3,
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

#[test]
fn to_repr_from_repr() {
    let repr: u32 = Color::Blue.into();
    let color = Color::from(repr);
    assert_eq!(color, Color::Blue);

    let repr: u32 = Color::Red.into();
    let color = Color::from(repr);
    assert_eq!(color, Color::Red);
}

#[test]
fn try_from_known_repr() {
    #[cfg(feature = "std")]
    {
        let known: u32 = ColorWithFeatures::Orange.into();
        let res = ColorWithFeatures::try_from(known);
        assert!(matches!(res, Ok(ColorWithFeatures::Orange)));
    }

    #[cfg(not(feature = "std"))]
    {
        let unknown: u32 = 3; // should match value of Orange in def to make sure we exclude
        let res = ColorWithFeatures::try_from(unknown);
        assert!(matches!(res, Err(TryFromKnownReprError)));
    }

    let known: u32 = ColorWithFeatures::Red.into();
    let res = ColorWithFeatures::try_from(known);
    assert!(matches!(res, Ok(ColorWithFeatures::Red)));

    let unknown: u32 = 100;
    let res = ColorWithFeatures::try_from(unknown);
    assert!(matches!(res, Err(TryFromKnownReprError)));
}
