extern crate open_enum;
use open_enum::open_enum;

#[open_enum]
enum DuplicateVariant {
    A = 1,
    B = 2,
    C = 1,
}

#[open_enum(allow_alias = false)]
enum ImplicitDuplicateVariant {
    A = 0,
    B = -1,
    C,
}

fn main() {}
