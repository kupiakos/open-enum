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
use open_enum::open_enum;

#[open_enum(allow_alias = pub(crate))]
pub enum Foo {
    Bar,
}

#[open_enum(not_a_real_option)]
pub enum Fizz {
    Buzz,
}

#[open_enum(inner_vis = "true")]
pub enum Alpha {
    Bet,
}

#[open_enum(allow_alias = true, allow_alias = false)]
pub enum Nine {
    Tales,
}

fn main() {}
