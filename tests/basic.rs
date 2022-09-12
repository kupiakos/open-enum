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

extern crate open_enum;
use open_enum::*;

#[open_enum]
enum Fruit {
    Apple,
    Pear,
    Banana,
    Blueberry = 5,
    Raspberry,
}

#[open_enum]
#[derive(PartialEq, Eq)]
enum AlreadyDerivesEq {
    Fizz,
    Buzz,
}

#[open_enum]
#[derive(Hash)]
enum HasHash {
    Lemon,
}

#[open_enum]
#[repr(i32)]
enum ExplicitRepr {
    Blah,
    Boo,
}

#[open_enum]
enum NegativeDiscriminant {
    What = -5,
    The = -2,
    Minus,
}

#[open_enum(allow_alias)]
enum Color {
    Red = 0,
    Blue,
    Crimson = 0,
    Azure,
}

#[open_enum(allow_alias = true, inner_vis = pub(crate))]
enum Color2 {
    Green = 0,
    Purple,
    Emerald = 0,
    Violet,
}

#[test]
fn values() {
    assert_eq!(Fruit::Apple.0, 0);
    assert_eq!(Fruit::Pear.0, 1);
    assert_eq!(Fruit::Banana.0, 2);
    assert_eq!(Fruit::Blueberry.0, 5);
    assert_eq!(Fruit::Raspberry.0, 6);

    assert_eq!(AlreadyDerivesEq::Fizz.0, 0);
    assert_eq!(AlreadyDerivesEq::Buzz.0, 1);

    assert_eq!(ExplicitRepr::Blah.0, 0);
    assert_eq!(ExplicitRepr::Boo.0, 1);

    assert_eq!(NegativeDiscriminant::What.0, -5);
    assert_eq!(NegativeDiscriminant::The.0, -2);
    assert_eq!(NegativeDiscriminant::Minus.0, -1);

    assert_eq!(Color::Red.0, 0);
    assert_eq!(Color::Crimson.0, 0);
    assert_eq!(Color::Blue.0, 1);
    assert_eq!(Color::Azure.0, 1);
}

#[test]
fn match_() {
    let _f = Fruit::Blueberry;
    for (fruit, expected) in [(Fruit::Apple, "apple"), (Fruit(20), "unknown fruit 20")] {
        let fruit_str = match fruit {
            Fruit::Apple => "apple".to_string(),
            Fruit::Pear => "pear".to_string(),
            Fruit::Banana => "banana".to_string(),
            Fruit::Blueberry => "blueberry".to_string(),
            Fruit::Raspberry => "raspberry".to_string(),
            Fruit(x) => format!("unknown fruit {x}"),
        };
        assert_eq!(fruit_str, expected);
    }
}

#[test]
fn explicit_repr() {
    let _x: i32 = ExplicitRepr::Blah.0;
}

#[test]
fn other_derive() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hash;
    let mut hasher = DefaultHasher::new();
    HasHash::Lemon.hash(&mut hasher);
    HasHash(20).hash(&mut hasher);
}

#[cfg(any(feature = "libc", feature = "std"))]
#[test]
fn repr_c() {
    use core::mem::size_of;

    #[repr(C)]
    #[open_enum]
    enum AnimalSound {
        Moo,
        Honk,
        Bahhh,
    }

    assert_eq!(AnimalSound::Moo.0, 0);
    assert_eq!(
        size_of::<AnimalSound>(),
        size_of::<open_enum::__private::c_int>()
    );
}

#[test]
fn pub_() {
    mod internal {
        use super::open_enum;

        #[open_enum]
        pub enum Foo {
            Bar,
        }
    }
    assert_eq!(internal::Foo::Bar.0, 0);
}

#[test]
fn empty_enum() {
    #[open_enum]
    #[repr(u64)]
    enum EmptyExplicitRepr {}

    assert_eq!(EmptyExplicitRepr(10).0, 10u64);

    #[open_enum]
    enum Empty {}

    // Current impl falls back to `isize` - this is not guaranteed.
    assert_eq!(Empty(10).0, 10);
}
