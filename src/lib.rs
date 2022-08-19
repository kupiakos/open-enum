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

//! Rust enums are _closed_, meaning that the integer value distinguishing an enum, its _discriminant_,
//! must be one of the variants listed. If the integer value isn't one of those discriminants, it
//! is considered immediate [undefined behavior][ub]. This is true for enums with and without fields.
//! This can make working with enums troublesome in high performance code that can't afford premature
//! runtime checks.
//! It can also introduce Undefined Behavior at unexpected times if the author is unfamiliar with
//! the [rules of writing `unsafe` Rust][nomicon].
//!
//! In constrast, C++ [scoped enumerations][cpp-scoped-enum] are _open_, meaning that the enum is a
//! strongly-typed integer that could hold any value, though with a scoped set of well-known values.
//! `open_enum` lets you have this in Rust. It turns this enum declaration:
//!
//! ```
//! # use open_enum::open_enum;
//! #[open_enum]
//! enum Color {
//!     Red,
//!     Green,
//!     Blue,
//!     Orange,
//!     Black,
//! }
//! ```
//!
//! into a tuple struct with associated constants:
//!
//! ```
//! #[derive(PartialEq, Eq)]  // In order to work in `match`
//! struct Color(pub u8);
//!
//! impl Color {
//!     pub const Red: Self = Color(0);
//!     pub const Green: Self = Color(1);
//!     pub const Blue: Self = Color(2);
//!     pub const Orange: Self = Color(3);
//!     pub const Black: Self = Color(4);
//! }
//! ```
//! 
//! There are clear readability benefits to using field-less `enum`s to represent integer data.
//! It provides more type safety than a raw integer, the `enum` syntax is consise, and it provides a
//! set of constants grouped under a type that can have methods.
//!
//! # Usage
//! Usage is similar to regular `enum`s, but with some key differences.
//!
//! ```
//! # use open_enum::open_enum;
//! # #[open_enum]
//! # #[derive(Debug)]
//! # enum Color {
//! #     Red,
//! #     Green,
//! #     Blue,
//! #     Orange,
//! #     Black,
//! # }
//! // Construct an open enum with the same `EnumName::VariantName` syntax.
//! let mut blood_of_angry_men = Color::Red;
//!
//! // Access the integer value with `.0`.
//! // This does not work: `Color::Red as u8`.
//! assert_eq!(blood_of_angry_men.0, 0);
//!
//! // Construct an open enum with an arbitrary integer value like any tuple struct.
//! let dark_of_ages_past = Color(4);
//!
//! // open enums always implement `PartialEq` and `Eq`, unlike regular enums.
//! assert_eq!(dark_of_ages_past, Color::Black);
//!
//! // This is outside of the known colors - but that's OK!
//! let this_is_fine = Color(10);
//!
//! // A match is always non-exhaustive - requiring a wildcard branch.
//! match this_is_fine {
//!     Color::Red => panic!("a world about to dawn"),
//!     Color::Green => panic!("grass"),
//!     Color::Blue => panic!("蒼: not to be confused with 緑"),
//!     Color::Orange => panic!("fun fact: the fruit name came first"),
//!     Color::Black => panic!("the night that ends at last"),
//!     // Wildcard branch, if we don't recognize the value. `x =>` also works.
//!     Color(value) => assert_eq!(value, 10),
//! }
//!
//! // Unlike a regular enum, you can pass the discriminant value as a reference.
//! fn increment(x: &mut i8) {
//!     *x += 1;
//! }
//!
//! increment(&mut blood_of_angry_men.0);
//! // These aren't men, they're skinks!
//! assert_eq!(blood_of_angry_men, Color::Green);
//!
//! ```
//!
//! # Integer type
//! `open_enum` will automatically determine an appropriately sized integer[^its-all-isize] to
//! represent the enum, if possible[^nonliterals-are-hard]. To choose a specific representation, it's the same
//! as a regular `enum`: add `#[repr(type)]`.
//! You can also specify `#[repr(C)]` to choose a C `int`.
//!
//!
//! ```
//! # use open_enum::open_enum;
//! #[open_enum]
//! #[repr(i16)]
//! #[derive(Debug)]
//! enum Fruit {
//!     Apple,
//!     Banana,
//!     Kumquat,
//!     Orange,
//! }
//!
//! assert_eq!(Fruit::Banana.0, 1i16);
//! assert_eq!(Fruit::Kumquat, Fruit(2));
//!
//! ```
//!  <div class="example-wrap" style="display:inline-block"><pre class="compile_fail" style="white-space:normal;font:inherit;">
//!
//!  **Warning**: `open_enum` may change the automatic integer representation for a given enum
//! in a future version with a minor version bump - it is not considered a breaking change.
//! Do not depend on this type remaining stable - use an explicit `#[repr]` for stability.
//!
//! </pre></div>
//! 
//! [^its-all-isize]: Like regular `enum`s, the declared discriminant for enums without an explicit `repr`
//! is interpreted as an `isize` regardless of the automatic storage type chosen.
//!
//! [^nonliterals-are-hard]: This optimization fails if the `enum` declares a non-literal constant expression
//! as one of its discriminant values, and falls back to `isize`. To avoid this, specify an explicit `repr`.
//!
//! # Aliasing variants
//! Regular `enum`s cannot have multiple variants with the same discriminant.
//! However, since `open_enum` produces associated constants, multiple
//! names can represent the same integer value. By default, `open_enum`
//! rejects aliasing variants, but it can be allowed with the `allow_alias` option:
//!
//! ```
//! # use open_enum::open_enum;
//! #[open_enum(allow_alias)]
//! #[derive(Debug)]
//! enum Character {
//!     Viola = 0,
//!     Cesario = 0,
//!     Sebastian,
//!     Orsino,
//!     Olivia,
//!     Malvolio,
//! }
//!
//! assert_eq!(Character::Viola, Character::Cesario);
//!
//! ```
//!
//! # Compared with `#[non_exhuastive]`
//! The [`non_exhaustive`][non-exhaustive] attribute indicates that a type or variant
//! may have more fields or variants added in the future. When applied to an `enum` (not its variants),
//! it requires that foreign crates provide a wildcard arm when `match`ing.
//! Since open enums are inherently non-exhaustive[^mostly-non-exhaustive], this attribute is incompatible
//! with `open_enum`. Unlike `non_exhaustive`, open enums also require a wildcard branch on `match`es in
//! the defining crate.
//!
//! [^mostly-non-exhaustive]: Unless the enum defines a variant for every value of its underlying integer.
//!
//! # Disadvantages
//! - No niche optimization: `Option<Color>` is 1 byte as a regular enum,
//!   but 2 bytes as an open enum.
//! - No pattern-matching assistance in rust-analyzer.
//! - You must have a wildcard case when pattern matching.
//! - `match`es that exist elsewhere won't break when you add a new variant,
//!   similar to `#[non_exhaustive]`. However, it also means you may accidentally
//!   forget to fill out a branch arm.
//!
//!
//! [cpp-scoped-enum]: https://en.cppreference.com/w/cpp/language/enum#Scoped_enumerations
//! [nomicon]: https://doc.rust-lang.org/nomicon/
//! [non-exhaustive]: https://doc.rust-lang.org/reference/attributes/type_system.html#the-non_exhaustive-attribute
//! [ub]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html

#![no_std]

pub use open_enum_derive::open_enum;

/// Utility functions only to be used by macros. Do not expect API stability.
#[doc(hidden)]
pub mod __private {

    pub use libc::c_int;

    /// A vector that's usable at `const fn` time (CTFE).
    struct ConstVec<T, const MAX_LEN: usize> {
        data: [T; MAX_LEN],
        len: usize,
    }

    impl<T: Copy, const MAX_LEN: usize> ConstVec<T, MAX_LEN> {
        const fn new(fill_val: T) -> Self {
            Self {
                data: [fill_val; MAX_LEN],
                len: 0,
            }
        }

        const fn push(mut self, val: T) -> Self {
            assert!(self.len < MAX_LEN, "push while full");
            self.data[self.len] = val;
            self.len += 1;
            self
        }

        const fn pop(mut self) -> (Self, T) {
            assert!(self.len > 0, "pop while empty");
            self.len -= 1;
            let val = self.data[self.len];
            (self, val)
        }

        const fn is_empty(&self) -> bool {
            self.len == 0
        }
    }

    macro_rules! no_duplicates {
        ($($t:tt),* $(,)?) => {
            no_duplicates!($($t => $t),*);
        };
        ($($name:ident => $t:ty),* $(,)?) => {
            $(
                paste::paste!(
                    // const generic over size so we can mutate the input in-place - &mut isn't usable in CTFE
                    #[allow(non_snake_case)]
                    pub const fn [<no_duplicates_ $name>]<const N: usize>(mut input: [$t; N]) -> bool {
                        if N <= 1 {
                            return true;
                        }
                        // https://en.wikipedia.org/wiki/Pigeonhole_principle
                        if ($t::MAX as i128) < N as i128 {
                            return false;
                        }
                        // There are a few ways to implement a duplicate-finding function in CTFE.
                        // Since we can't allocate or &mut, we need to know all of the space we'll
                        // need ahead of time. So, no hash sets.
                        // The easiest is the naive O(N^2) algorithm, for all i 0..N, j (i+1)..N: i != j
                        // However, there's a more efficient way: sort, then for all i: 1..N (i - 1) != i.
                        // With a bubble sort, it's still O(N^2), but with much better performance for mostly-sorted
                        // arrays as would most likely occur for the input data.
                        // Instead though, let's go all out and do quicksort, O(N log N).
                        let mut lo = 0;
                        let mut hi = (N - 1);

                        // We actually only need log2(N), but we're not good enough for that in CTFE.
                        let mut stack = ConstVec::<_, N>::new((0, 0));
                        stack = stack.push((lo, hi));

                        while !stack.is_empty() {
                            (stack, (lo, hi)) = stack.pop();

                            let p = {
                                // hoare's partition scheme
                                let pivot = input[(hi + lo) / 2];

                                let mut i = lo.wrapping_sub(1);
                                let mut j = hi + 1;
                                loop {
                                    i = i.wrapping_add(1);
                                    while input[i] < pivot {
                                        i += 1;
                                    }
                                    j -= 1;
                                    while input[j] > pivot {
                                        j -= 1;
                                    }
                                    if i >= j { break j }
                                    let tmp = input[i];
                                    input[i] = input[j];
                                    input[j] = tmp;
                                }
                            };

                            // recurse into partitions
                            if p > 0 && p - 1 > lo {
                                stack = stack.push((lo, p));
                            }

                            if p + 1 < hi {
                                stack = stack.push((p + 1, hi));
                            }
                        }

                        // Now that the array is sorted - see if there are any adjacent equal elements.
                        let mut i = 1;
                        while i < N {
                            if input[i - 1] == input[i] {
                                return false;
                            }
                            i += 1;
                        }
                        true
                    }
                );
            )*
        };
    }

    no_duplicates!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize);
    no_duplicates!(C => c_int);

    #[cfg(test)]
    mod tests {
        use super::{no_duplicates_u8, no_duplicates_i8};

        #[test]
        fn test_dupes() {
            assert!(no_duplicates_u8([]));
            assert!(no_duplicates_u8([0]));
            assert!(no_duplicates_u8([0, 1]));
            assert!(no_duplicates_u8([0, 1, 2, 3]));
            assert!(no_duplicates_u8([3, 2, 1, 0]));
            assert!(!no_duplicates_u8([0, 0]));
            assert!(!no_duplicates_u8([0, 1, 2, 0]));
            assert!(!no_duplicates_u8([2, 1, 2, 0]));
            assert!(!no_duplicates_i8([2, 1, 2, 0, 9, -5, 3]));
        }
    }
}
