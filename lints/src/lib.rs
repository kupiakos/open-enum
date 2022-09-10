//! This package exists to test the linting behavior of open enums.
//! TODO: target `cargo clippy`

/// Tests missing_docs
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
