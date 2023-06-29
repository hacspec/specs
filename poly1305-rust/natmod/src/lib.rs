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
use syn::{parse::Parse, parse_macro_input, DeriveInput, Ident, LitInt, LitStr, Result, Token};

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
    let static_name = Ident::new(
        &format!("{}_MODULUS_STR", ident.to_string().to_uppercase()),
        ident.span(),
    );

    let out_struct = quote! {
        // #[hax(...)]
        #[derive(Clone, Copy)]
        pub struct #ident {
            value: [u8; #num_bytes],
        }

        //#[not_hax]
        // mod #ident_mod {

        // }

        const #const_name: [u8; #num_bytes] = [#(#mod_iter1),*];
        static #static_name: &str = #modulus_string;

        impl NatMod<#ident> for #ident {
            const MODULUS: #ident = #ident {
                value: [#(#mod_iter2),*]
            };
            const MODULUS_STR: &'static str = #modulus_string;
        }

        impl #ident {
            /// Get the modulus as string
            pub const fn modulus_string() -> &'static str {
                #modulus_string
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

            /// Get hex string representation of this.
            pub fn to_hex(&self) -> String {
                let strs: Vec<String> = self.value.iter().map(|b| format!("{:02x}", b)).collect();
                strs.join("")
            }

            /// Zero element
            pub const fn zero() -> Self {
                Self {
                    value: [0u8; #num_bytes]
                }
            }

            /// Returns 2 to the power of the argument
            pub fn pow2(x: usize) -> Self {
                let res = num_bigint::BigUint::from(1u32) << x;
                res.into()
            }

            /// Create a new [`#ident`] from a `u128` literal.
            pub fn from_u128(literal: u128) -> Self {
                Self::from(num_bigint::BigUint::from(literal))
            }

            /// Create a new [`#ident`] from a little endian byte slice.
            pub fn from_le_bytes(bytes: &[u8]) -> Self {
                Self::from(num_bigint::BigUint::from_bytes_le(bytes))
            }

            /// Create a new [`#ident`] from a little endian byte slice.
            pub fn from_be_bytes(bytes: &[u8]) -> Self {
                Self::from(num_bigint::BigUint::from_bytes_be(bytes))
            }

            pub fn to_le_bytes(self) -> [u8; #num_bytes] {
                pad(&num_bigint::BigUint::from_bytes_be(&self.value).to_bytes_le())
            }
        }

        fn pad(bytes: &[u8]) -> [u8; #num_bytes] {
            let mut value = [0u8; #num_bytes];
            let upper = value.len();
            let lower = upper - bytes.len();
            value[lower..upper].copy_from_slice(&bytes);
            value
        }

        impl From<num_bigint::BigUint> for #ident {
            fn from(x: num_bigint::BigUint) -> #ident {
                let max_value = Self::modulus();
                assert!(x <= num_bigint::BigUint::from_bytes_be(&max_value), "{} is too large for type {}!", x, stringify!($ident));
                let repr = x.to_bytes_be();
                if repr.len() > #num_bytes {
                    panic!("{} is too large for type {}", x, stringify!(#ident))
                }

                Self {
                    value: pad(&repr)
                }
            }
        }

        impl core::convert::AsRef<[u8]> for #ident {
            fn as_ref(&self) -> &[u8] {
                &self.value
            }
        }

        impl core::fmt::Display for #ident {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}", self.to_hex())
            }
        }

        impl core::ops::Add for #ident {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                let lhs = num_bigint::BigUint::from_bytes_be(&self.value);
                let rhs = num_bigint::BigUint::from_bytes_be(&rhs.value);
                let modulus = num_bigint::BigUint::from_bytes_be(&Self::modulus());
                let res = (lhs + rhs) % modulus;
                let res = res.to_bytes_be();
                assert!(res.len() <= #num_bytes);
                let mut value = Self::zero();
                let offset = #num_bytes-res.len();
                for i in 0..res.len() {
                    value.value[offset+i] = res[i];
                }
                value
            }
        }


        impl core::ops::Mul for #ident {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                let lhs = num_bigint::BigUint::from_bytes_be(&self.value);
                let rhs = num_bigint::BigUint::from_bytes_be(&rhs.value);
                let modulus = num_bigint::BigUint::from_bytes_be(&Self::modulus());
                let res = (lhs * rhs) % modulus;
                let res = res.to_bytes_be();
                assert!(res.len() <= #num_bytes);
                let mut value = Self::zero();
                let offset = #num_bytes-res.len();
                for i in 0..res.len() {
                    value.value[offset+i] = res[i];
                }
                value
            }
        }
    };

    out_struct.into()
}
