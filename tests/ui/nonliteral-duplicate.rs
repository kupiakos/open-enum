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

// This is a separate test case from duplicate.rs since the error messages
// occur at different points of compilation.

const ONE: isize = 1;

#[open_enum]
enum NonLiteralDuplicateVariant {
    A = 1,
    B = 2,
    C = ONE,
}

#[open_enum]
enum NonLiteralImplicitDuplicateVariant {
    A = ONE,
    B = 0,
    C,
}

fn main() {}
