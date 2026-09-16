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
