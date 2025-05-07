#![no_std]
#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;

#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;

// use hax_lib::lemma;

#[exclude]
use core::iter::Product;
#[exclude]
use core::marker::Copy;
#[exclude]
use core::ops::{Add, Mul, Neg};

////////////
// Traits //
////////////

/** Interface for field implementation */
pub trait Field:
    Copy
    + PartialEq
    + Eq
    + Clone
    + Copy
    + hacspec_concordium::Serialize
    + Mul<Output = Self>
    + Product
    + Add<Output = Self>
    + Neg<Output = Self>
{
    fn q() -> Self;

    fn random_field_elem(random: u32) -> Self;

    fn field_zero() -> Self;
    fn field_one() -> Self;

    fn inv(x: Self) -> Self;
}

/** Interface for group implementation */
pub trait Group:
    Copy + PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize + Mul<Output = Self> + Product
{
    type Z: Field;

    fn g() -> Self; // Generator (elemnent of group)

    fn g_pow(x: Self::Z) -> Self;
    fn pow(g: Self, x: Self::Z) -> Self; // TODO: Link with q
    fn group_one() -> Self;
    fn group_inv(x: Self) -> Self;

    fn hash(x: Vec<Self>) -> Self::Z;
}
