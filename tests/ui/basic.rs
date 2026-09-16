
extern crate open_enum;
use open_enum::open_enum;

#[open_enum]
enum Color {
    Red,
    Blue,
    Green(u32),
}

#[open_enum]
enum Foo {
    Bar,
    Bin { field: u32 },
    Baz,
}


#[open_enum]
#[repr(u128)]
enum A {
    A,
    B,
    C,
}

#[open_enum]
#[repr(i128)]
enum B {
    A,
    B,
    C
}

#[open_enum]
enum C<T> {
    A,
    B,
    C
}

#[open_enum(foo)]
enum D {}

#[open_enum]
#[non_exhaustive]
enum E {
    A = 1,
}

fn main() {}
