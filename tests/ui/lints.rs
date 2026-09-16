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
