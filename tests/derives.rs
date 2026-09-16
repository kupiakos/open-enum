// `ColorWithFeatures` below intentionally uses a nonexistent `orange` feature to
// check that `#[cfg(...)]` is propagated to the generated items.
#![allow(unexpected_cfgs)]

extern crate open_enum;
use open_enum::*;
use test_derive_helper_attr::WithTestAttr;

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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum ColorWithFeatures {
    Red = 1,
    Blue = 2,
    /// Test doc
    #[cfg(feature = "orange")]
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

// Fails to build if test_attr is re-ordered above derive attrs.
#[open_enum]
#[derive(WithTestAttr)]
#[test_attr]
enum AttrOrder {}
