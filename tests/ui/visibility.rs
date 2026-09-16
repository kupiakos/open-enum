extern crate open_enum;

pub mod access_limit {
    pub mod inner {
        #[open_enum::open_enum(inner_vis = pub(super))]
        pub enum Foo {
            Bar,
            Baz,
        }
    }
    const _ShouldCompile: () = assert!(inner::Foo::Bar.0 == 0);
}

const _ShouldFail: () = assert!(access_limit::inner::Foo::Bar.0 == 0);

fn main() {}
// const _:
