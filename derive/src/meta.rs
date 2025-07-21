use proc_macro2::Ident;
use quote::quote;
use quote::ToTokens;
use quote::TokenStreamExt;
use syn::meta::ParseNestedMeta;
use syn::parse::Parse;
use syn::parse_quote;
use syn::spanned::Spanned;
use syn::Attribute;
use syn::Error;
use syn::Expr;
use syn::LitStr;
use syn::Path;

use crate::Discriminant;
use crate::Repr;

pub struct Metadata {
    pub repr: Repr,
    pub variants: Vec<Variant>,
}
impl Metadata {
    #[allow(dead_code)]
    pub fn from_attribute(attr: Attribute) -> syn::Result<Self> {
        let expected_path: Path = parse_quote!(open_enum_meta);
        if attr.path() != &expected_path {
            return Err(Error::new(
                attr.span(),
                "unexpected attribute name (should be open_enum_meta",
            ));
        }
        let mut variants = vec![];
        let mut repr: Option<Repr> = None;
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("variant") {
                variants.push(Variant::parse(meta)?);
            } else if meta.path.is_ident("repr") {
                set_argument(&meta, "repr", &mut repr, Repr::parse(meta.value()?)?)?;
            }
            Ok(())
        })?;
        let repr = repr.ok_or_else(|| Error::new(attr.path().span(), "missing field 'repr'"))?;
        Ok(Metadata { repr, variants })
    }
}

impl ToTokens for Metadata {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let repr = self.repr;
        let variants = self.variants.iter();
        tokens.append_all(quote! {
            #[open_enum_meta(
                repr = #repr,
                #(#variants),*
            )]
        });
    }
}

pub struct Variant {
    pub ident: Ident,
    pub name: String,
    pub value: Discriminant,
    pub attrs: Vec<Attribute>,
}
impl Variant {
    fn parse(meta: ParseNestedMeta) -> syn::Result<Self> {
        if !meta.path.is_ident("variant") {
            return Err(Error::new(
                meta.path.span(),
                "unexpected attribute (expected \"variant\")",
            ));
        }
        let mut ident: Option<Ident> = None;
        let mut name: Option<String> = None;
        let mut value: Option<Discriminant> = None;
        let mut attrs = Vec::<Attribute>::new();
        meta.parse_nested_meta(|meta| {
            if meta.path.is_ident("ident") {
                set_argument(&meta, "ident", &mut ident, meta.value()?.parse()?)?;
            }
            if meta.path.is_ident("name") {
                set_argument(
                    &meta,
                    "name",
                    &mut name,
                    meta.value()?.parse::<LitStr>()?.value(),
                )?;
            }
            if meta.path.is_ident("value") {
                set_argument(
                    &meta,
                    "value",
                    &mut value,
                    Discriminant::new(meta.value()?.parse::<Expr>()?)?,
                )?;
            }
            if meta.path.is_ident("attrs") {
                let content;
                syn::parenthesized!(content in meta.input);
                attrs = Attribute::parse_outer(&content)?;
            }
            Ok(())
        })
        .unwrap();
        let ident = ident.ok_or_else(|| Error::new(meta.path.span(), "missing field 'ident'"))?;
        let name = name.ok_or_else(|| Error::new(meta.path.span(), "missing field 'name'"))?;
        let value = value.ok_or_else(|| Error::new(meta.path.span(), "missing field 'value'"))?;
        Ok(Variant {
            ident,
            name,
            value,
            attrs,
        })
    }
}
impl ToTokens for Variant {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let ident = &self.ident;
        let name = &self.name;
        let value = &self.value;
        let attrs = &self.attrs;
        tokens.append_all(quote! {
            variant(ident = #ident, name = #name, value = #value, attrs(#(#attrs)*))
        });
    }
}

fn set_argument<T>(
    meta: &ParseNestedMeta,
    name: &str,
    opt: &mut Option<T>,
    val: T,
) -> syn::Result<()> {
    if let Some(_existing) = opt.replace(val) {
        return Err(Error::new(
            meta.path.span(),
            format!("duplicate argument {name:?}"),
        ));
    }
    Ok(())
}
#[cfg(test)]
mod test {
    use super::*;

    use quote::{format_ident, quote};
    use syn::{parse_quote, Attribute};

    #[test]
    pub fn test() {
        let attr: Attribute = parse_quote! {
            #[open_enum_meta(
                repr = u32,
                variant(
                    ident = Orange,
                    name = "ORANGE",
                    value = 3,
                    attrs(
                        #[doc = " Test doc"]
                        #[cfg(feature = "orange")]
                    )
                ),
                variant(
                    value = FOO + 4,
                    name = "RED",
                    attrs(
                        #[foo = 5 + 2]
                    ),
                    ident = Red,
                ),
                variant(
                    ident = Blue,
                    name = "blue",
                    value = BLUE_INDEX,
                )
            )]
        };
        let meta = Metadata::from_attribute(attr.clone()).unwrap();
        assert!(matches!(meta.repr, Repr::U32));
        assert_eq!(meta.variants.len(), 3);
        assert_eq!(meta.variants[0].ident, format_ident!("Orange"));
        assert_eq!(meta.variants[0].name, "ORANGE");
        assert!(matches!(meta.variants[0].value, Discriminant::Literal(3)));
        assert_eq!(meta.variants[0].attrs.len(), 2);
        assert_eq!(
            meta.variants[0].attrs[0].to_token_stream().to_string(),
            quote!(#[doc = " Test doc"]).to_string()
        );
        assert_eq!(
            meta.variants[0].attrs[1].to_token_stream().to_string(),
            quote!(#[cfg(feature = "orange")]).to_string()
        );

        assert_eq!(meta.variants[1].ident, format_ident!("Red"));
        assert_eq!(meta.variants[1].name, "RED");
        assert_eq!(
            meta.variants[1].value.to_token_stream().to_string(),
            "FOO + 4"
        );
        assert_eq!(meta.variants[1].attrs.len(), 1);
        assert_eq!(
            meta.variants[1].attrs[0].to_token_stream().to_string(),
            quote!(#[foo = 5 + 2]).to_string()
        );

        assert_eq!(meta.variants[2].ident, format_ident!("Blue"));
        assert_eq!(meta.variants[2].name, "blue");
        assert_eq!(
            meta.variants[2].value.to_token_stream().to_string(),
            "BLUE_INDEX"
        );
        assert_eq!(meta.variants[2].attrs.len(), 0);

        assert_eq!(
            meta.to_token_stream().to_string(),
            quote! {
                #[open_enum_meta(
                    repr = u32,
                    variant(
                        ident = Orange,
                        name = "ORANGE",
                        value = 3,
                        attrs(
                            #[doc = " Test doc"]
                            #[cfg(feature = "orange")]
                        )
                    ),
                    variant(
                        ident = Red,
                        name = "RED",
                        value = FOO + 4,
                        attrs(
                            #[foo = 5 + 2]
                        )
                    ),
                    variant(
                        ident = Blue,
                        name = "blue",
                        value = BLUE_INDEX,
                        attrs()
                    )
                )]
            }
            .to_string()
        );
    }
}
