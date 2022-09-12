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

pub mod access_limit {
    pub mod inner {
        #[open_enum::open_enum(inner_vis = pub(super))]
        pub enum Foo {
            Bar,
            Baz,
        }
    }
    const _ShouldCompile: () = assert!(inner::Foo::Bar.0 == 0);
}

const _ShouldFail: () = assert!(access_limit::inner::Foo::Bar.0 == 0);

fn main() {}
// const _:
