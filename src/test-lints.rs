//! Tests lints that should compile.
//!
//! Tests (unit or integration) don't trigger missing_docs, so this must be a binary or library.
//! Binary is simpler. Alternatively, this could be part of the ui/compile-fail test fixture.

/// Tests that basic attributes propagate, like documentation.
pub mod docs {
    #![deny(missing_docs)]
    use open_enum::open_enum;

    #[open_enum]
    /// This struct has documentation.
    pub enum ImportantLetters {
        /// A is the first letter of the English alphabet.
        A,

        /// B is for Bananaphone.
        B,
    }
}

/// Tests that allow lints propagate through an open enum definition correctly.
pub mod allow_lint_propagates {
    #![deny(missing_docs)]
    use open_enum::open_enum;

    // Checks that local lints propagate correctly.
    #[open_enum]
    #[allow(missing_docs)]
    pub enum HasLintTop {
        A,
        B,
    }

    #[allow(missing_docs)]
    #[open_enum]
    pub enum HasLintBottom {
        A,
        B,
    }
}

pub mod clippy {
    // We should pass this, as this is a newtype.
    #![deny(clippy::exhaustive_structs)]

    #[open_enum::open_enum]
    pub enum Foo {
        Bar,
        Baz,
    }
}

pub mod nonliteral {
    #![deny(dead_code)]

    #[open_enum::open_enum]
    #[derive(PartialEq, Eq)] // for some reason this has to be here to get a dead_code lint to trigger
    #[repr(u32)]
    pub enum Fuzz {
        Balls = 1 << 1,
    }
}

fn main() {}
