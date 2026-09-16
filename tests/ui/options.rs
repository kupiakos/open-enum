extern crate open_enum;
use open_enum::open_enum;

#[open_enum(allow_alias = pub(crate))]
pub enum Foo {
    Bar,
}

#[open_enum(not_a_real_option)]
pub enum Fizz {
    Buzz,
}

#[open_enum(inner_vis = "true")]
pub enum Alpha {
    Bet,
}

#[open_enum(allow_alias = true, allow_alias = false)]
pub enum Nine {
    Tales,
}

fn main() {}
