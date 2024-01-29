#![no_std]
#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;

#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

////////////
// Traits //
////////////

pub trait Z_Field: core::marker::Copy {
    type field_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

    fn q() -> Self::field_type;

    fn random_field_elem(random: u32) -> Self::field_type;

    fn field_zero() -> Self::field_type;
    fn field_one() -> Self::field_type;

    fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type;
    fn sub(x: Self::field_type, y: Self::field_type) -> Self::field_type;
    fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type;
}

/** Interface for group implementation */
pub trait Group<Z: Z_Field>: core::marker::Copy {
    type group_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

    fn g() -> Self::group_type; // Generator (elemnent of group)

    fn g_pow(x: Z::field_type) -> Self::group_type;
    fn pow(g: Self::group_type, x: Z::field_type) -> Self::group_type; // TODO: Link with q
    fn group_one() -> Self::group_type;
    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type;
    fn inv(x: Self::group_type) -> Self::group_type;
    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type;

    fn hash(x: Vec<Self::group_type>) -> Z::field_type;
}
