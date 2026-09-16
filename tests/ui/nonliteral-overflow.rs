extern crate open_enum;

#[open_enum::open_enum]
#[repr(u8)]
enum NonLiteralImplicitOverflow {
    A = u8::MAX - 1,
    B,
    C,
}

// TODO: overflow isize with the implicit repr
fn main() {}
