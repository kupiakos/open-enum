# `open_enum`

Rust enums are _closed_, meaning that the integer value distinguishing an enum, its _discriminant_,
must be one of the variants listed. If the integer value isn't one of those discriminants, it
is considered immediate [undefined behavior][ub]. This is true for enums with and without fields.
This can make working with enums troublesome in high performance code that can't afford premature
runtime checks.
It can also introduce Undefined Behavior at unexpected times if the author is unfamiliar with
the [rules of writing `unsafe` Rust][nomicon].

In constrast, C++ [scoped enumerations][cpp-scoped-enum] are _open_, meaning that the enum is a
strongly-typed integer that could hold any value, though with a scoped set of well-known values.
`open_enum` lets you have this in Rust. It turns this enum declaration:

``` rust
#[open_enum]
enum Color {
    Red,
    Green,
    Blue,
    Orange,
    Black,
}
```

into a tuple struct with associated constants:

``` rust
#[derive(PartialEq, Eq)]  // In order to work in `match`
struct Color(pub u8);

impl Color {
    pub const Red: Self = Color(0);
    pub const Green: Self = Color(1);
    pub const Blue: Self = Color(2);
    pub const Orange: Self = Color(3);
    pub const Black: Self = Color(4);
}
```

[cpp-scoped-enum]: https://en.cppreference.com/w/cpp/language/enum#Scoped_enumerations
[nomicon]: https://doc.rust-lang.org/nomicon/
[ub]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
