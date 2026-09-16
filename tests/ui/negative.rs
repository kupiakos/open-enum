extern crate open_enum;
use open_enum::open_enum;

#[open_enum]
#[repr(u32)]
enum NegativeDiscriminantOnUnsignedValue {
    A = 0,
    B = -1,
}

fn main() {}
