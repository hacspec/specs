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

pub use crate::ovn_traits::*;

// // pub use create::ovn_traits::*;
// use create::Z_Field;
// use create::Group;
// use create::Z_Field;

////////////////////
// Impl for Z/89Z //
////////////////////

#[derive(Clone, Copy)]
pub struct z_89 {}
impl Z_Field for z_89 {
    type field_type = u32;
    fn q() -> Self::field_type {
        89u32
    } // Prime order
    fn random_field_elem(random: u32) -> Self::field_type {
        random % (Self::q() - 1)
    }

    fn field_zero() -> Self::field_type {
        0u32
    }

    fn field_one() -> Self::field_type {
        1u32
    }

    fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        (x + y) % (Self::q() - 1)
    }

    fn sub(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        (x + (Self::q() - 1) - y) % (Self::q() - 1)
    }

    fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        (x * y) % (Self::q() - 1)
    }
}

#[derive(Clone, Copy)]
pub struct g_z_89 {}
impl Group<z_89> for g_z_89 {
    type group_type = u32;

    fn g() -> Self::group_type {
        3u32
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self::group_type>) -> <z_89 as Z_Field>::field_type {
        let mut res = z_89::field_one();
        for y in x {
            res = z_89::mul(y, res);
        }
        res // TODO
    }

    fn g_pow(x: <z_89 as Z_Field>::field_type) -> Self::group_type {
        Self::pow(Self::g(), x)
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self::group_type, x: <z_89 as Z_Field>::field_type) -> Self::group_type {
        let mut result = Self::group_one();
        for i in 0..(x % (z_89::q() - 1)) {
            result = Self::prod(result, g);
        }
        result
    }

    fn group_one() -> Self::group_type {
        1
    }

    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        ((x % z_89::q()) * (y % z_89::q())) % z_89::q()
    }

    fn inv(x: Self::group_type) -> Self::group_type {
        for j in 0..89 {
            if Self::prod(x, j) == Self::group_one() {
                return j;
            }
        }
        assert!(false);
        return x;
    }

    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        Self::prod(x, Self::inv(y))
    }
}
