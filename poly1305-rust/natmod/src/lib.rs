//! // This trait lives in the library
//! pub trait NatModTrait<T> {
//!     const MODULUS: T;
//! }
//!
//! #[nat_mod("123456", 10)]
//! struct MyNatMod {}

use hex::FromHex;
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse::Parse, parse_macro_input, DeriveInput, Ident, LitInt, LitStr, Meta, Result, Token,
};

#[derive(Clone, Debug)]
struct NatModAttr {
    /// Modulus as hex string and bytes
    mod_str: String,
    mod_bytes: Vec<u8>,
    /// Number of bytes to use for the integer
    int_size: usize,
}

impl Parse for NatModAttr {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let mod_str = input.parse::<LitStr>()?.value();
        let mod_bytes = Vec::<u8>::from_hex(&mod_str).expect("Invalid hex String");
        input.parse::<Token![,]>()?;
        let int_size = input.parse::<LitInt>()?.base10_parse::<usize>()?;
        assert!(input.is_empty(), "Left over tokens in attribute {input:?}");
        Ok(NatModAttr {
            mod_str,
            mod_bytes,
            int_size,
        })
    }
}

#[proc_macro_attribute]
pub fn nat_mod(attr: TokenStream, item: TokenStream) -> TokenStream {
    let item_ast = parse_macro_input!(item as DeriveInput);
    let ident = item_ast.ident.clone();
    let args = parse_macro_input!(attr as NatModAttr);

    let num_bytes = args.int_size;
    let modulus = args.mod_bytes;
    let modulus_string = args.mod_str;

    let mut padded_modulus = vec![0u8; num_bytes - modulus.len()];
    padded_modulus.append(&mut modulus.clone());
    let mod_iter1 = padded_modulus.iter();
    let mod_iter2 = padded_modulus.iter();
    let mod_iter3 = padded_modulus.iter();
    let const_name = Ident::new(
        &format!("{}_MODULUS", ident.to_string().to_uppercase()),
        ident.span(),
    );

    let out_struct = quote! {
        pub struct #ident {
            value: [u8; #num_bytes],
        }

        pub const #const_name: [u8; #num_bytes] = [#(#mod_iter1),*];

        impl NatMod<#ident> for #ident {
            const MODULUS: #ident = #ident {
                value: [#(#mod_iter2),*]
            };
        }

        impl #ident {
            /// Get the modulus as string
            pub fn modulus_string() -> String {
                #modulus_string.to_string()
            }

            /// Get the modulus as byte array
            pub const fn modulus() -> [u8; #num_bytes] {
                [#(#mod_iter3),*]
            }

            /// New from hex string
            pub fn from_hex(hex: &str) -> Self {
                assert!(hex.len() % 2 == 0);
                let l = hex.len() / 2;
                assert!(l <= #num_bytes);
                let mut value = [0u8; #num_bytes];
                let skip = #num_bytes - l;
                for i in 0..l {
                    value[skip + i] =
                        u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("An unexpected error occurred.");
                }
                Self {
                    value
                }
            }

            /// Zero element
            pub const fn zero() -> Self {
                Self {
                    value: [0u8; #num_bytes]
                }
            }
        }

        impl core::convert::AsRef<[u8]> for #ident {
            fn as_ref(&self) -> &[u8] {
                &self.value
            }
        }

        impl core::ops::Add for #ident {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                let lhs = num_bigint::BigUint::from_bytes_be(&self.value);
                let rhs = num_bigint::BigUint::from_bytes_be(&rhs.value);
                let res = (lhs + rhs) % num_bigint::BigUint::from_bytes_be(&Self::modulus());
                Self {
                    value: res.to_bytes_be().try_into().unwrap()
                }
            }
        }
    };
    out_struct.into()
}
