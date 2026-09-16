extern crate open_enum;
use open_enum::open_enum;

#[open_enum]
enum InterpretsAsIsize {
    X = u8::MAX,
}

fn main() {}
