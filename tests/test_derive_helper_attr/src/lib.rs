use proc_macro::TokenStream;

#[proc_macro_derive(WithTestAttr, attributes(test_attr))]
pub fn derive_with_test_attr(_item: TokenStream) -> TokenStream {
    TokenStream::new()
}
