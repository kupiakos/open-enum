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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum Color3 {
    Red = 0x0,
    White = 0x1,
}

#[open_enum]
#[derive(core::fmt::Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum Color4 {
    Red = 0x0,
    White = 0x1,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct EmbeddedColor {
    pub color: Color3,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct EmbeddedColorExtension {
    pub color: Color4,
}

#[test]
fn embedded_enum_struct() {
    let test_struct = EmbeddedColor { color: Color3::Red };

    assert_eq!(test_struct.color, Color3::Red);

    let expected_debug_str = "EmbeddedColor { color: Red }";
    let debug_str = format!("{:?}", test_struct);

    assert_eq!(expected_debug_str, debug_str);
}

#[test]
fn extended_embedded_enum_struct() {
    let test_struct = EmbeddedColorExtension { color: Color4::Red };

    assert_eq!(test_struct.color, Color4::Red);

    let expected_debug_str = "EmbeddedColorExtension { color: Red }";
    let debug_str = format!("{:?}", test_struct);

    assert_eq!(expected_debug_str, debug_str);
}
