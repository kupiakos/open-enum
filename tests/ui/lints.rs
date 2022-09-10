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

//! Tests that failure lints are detected correctly on the
//! output of the proc macro.
#![deny(missing_docs)]

extern crate open_enum;

/// Tests that an outer #![deny(missing_docs)] is triggered for an open enum correctly.
pub mod outer_deny_errors {
    #![deny(missing_docs)]
    use open_enum::open_enum;

    #[open_enum]
    pub enum NoDocs {
        Round,
        Here,
    }
}

/// Tests that the #[deny] lint propagates correctly.
pub mod deny_lint_propagates {
    use open_enum::open_enum;

    #[open_enum]
    #[deny(missing_docs)]
    pub enum NoDocs {
        Round,
        Here,
    }
}

/// Tests that the #[warn] lint propagates correctly.
pub mod warn_lint_propagates {
    use open_enum::open_enum;

    #[warn(missing_docs)]
    #[open_enum]
    pub enum NoDocs {
        Round,
        Here,
    }
}

/// Tests that the #[forbid] lint propagates correctly.
pub mod forbid_lint_propagates {
    use open_enum::open_enum;

    #[open_enum]
    #[forbid(missing_docs)]
    pub enum NoDocs {
        Round,
        Here,
    }
}

fn main() {}
