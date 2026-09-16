extern crate open_enum;

#[open_enum::open_enum]
#[repr(u8)]
enum OverflowingLiteral {
    A = 0xffef,
    B,
}

#[open_enum::open_enum]
#[repr(u8)]
enum LiteralImplicitOverflow {
    A = 255,
    B,
}

// TODO: overflow isize with the implicit repr
fn main() {}
