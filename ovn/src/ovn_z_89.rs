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
// use create::Field;
// use create::Group;
// use create::Field;

////////////////////
// Impl for Z/89Z //
////////////////////

#[derive(Clone, Copy, PartialEq, Eq, hacspec_concordium::Serial, hacspec_concordium::Deserial)]
pub struct z_89 { z_val : u8 }

// impl hacspec_concordium::Deserial for z_89 {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v : u8 = source.get()?;
//         Ok(z_89 {
//             z_val: v,
//         })
//     }
// }

// impl hacspec_concordium::Serial for z_89 {
//     // TODO:
//     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
//         self.z_val.serial(out)
//     }
// }

impl core::ops::Mul for z_89 {
    type Output = Self;
    fn mul(self, y: Self) -> Self {
        let q_ = Self::q().z_val - 1;
        let x_ : u16 = (self.z_val % q_) as u16;
        let y_ : u16 = (y.z_val % q_) as u16;
        z_89{ z_val: ((x_ * y_) % (q_ as u16)) as u8 }
    }
}

impl core::iter::Product for z_89 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            z_89{ z_val: 1u8 },
            |a, b| a * b,
        )
    }
}

impl core::ops::Add for z_89 {
    type Output = Self;
    fn add(self, y: Self) -> Self {
        let q_ = Self::q().z_val - 1;
        let x_ = self.z_val % q_;
        let y_ = y.z_val % q_;
        z_89{ z_val: (x_ + y_) % q_ }
    }
}

impl core::ops::Neg for z_89 {
    type Output = Self;
    fn neg(self) -> Self {
        let q_ = Self::q().z_val - 1;
        let x_ = self.z_val % q_;
        z_89{ z_val: q_ - x_ }
    }
}

impl Field for z_89 {
    fn q() -> Self {
        z_89{ z_val: 89u8}
    } // Prime order
    fn random_field_elem(random: u32) -> Self {
        z_89{ z_val: random as u8 % (Self::q().z_val - 1) }
    }

    fn field_zero() -> Self {
        z_89{ z_val: 0u8 }
    }

    fn field_one() -> Self {
        z_89{ z_val: 1u8 }
    }

    fn inv(x: Self) -> Self {
        assert!(false); // Missing
        return x;

    }
}

#[derive(Clone, Copy, PartialEq, Eq, hacspec_concordium::Serial, hacspec_concordium::Deserial)]
pub struct g_z_89 { g_val : u8 }

// impl hacspec_concordium::Deserial for g_z_89 {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v : u8 = source.get()?;

//         Ok(g_z_89 {
//             g_val: v,
//         })
//     }
// }

// impl hacspec_concordium::Serial for g_z_89 {
//     // TODO:
//     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
//         self.g_val.serial(out)
//     }
// }

impl core::ops::Mul for g_z_89 {
    type Output = Self;
    fn mul(self, y: Self) -> Self {
        let q_ = z_89::q().z_val;
        let x_ = (self.g_val % q_) as u16;
        let y_ = (y.g_val % q_) as u16;
        g_z_89 { g_val: ((x_ * y_) % (q_ as u16)) as u8 }
    }
}

impl core::iter::Product for g_z_89 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            g_z_89 { g_val: 1 },
            |a, b| a * b,
        )
    }
}

impl Group for g_z_89 {
    type Z = z_89;

    fn g() -> Self {
        g_z_89 { g_val: 3u8 }
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self>) -> z_89 {
        let mut res = z_89::field_one();
        for y in x {
            res = z_89{z_val: y.g_val} * res;
        }
        res // TODO
    }

    fn g_pow(x: z_89) -> Self {
        Self::pow(Self::g(), x)
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self, x: z_89) -> Self {
        let mut result = Self::group_one();
        for _ in 0..(x.z_val % (z_89::q().z_val - 1)) {
            result = result * g;
        }
        result
    }

    fn group_one() -> Self {
        g_z_89 { g_val: 1 }
    }

    fn group_inv(x: Self) -> Self {
        for j in 0..89 {
            let g_value = g_z_89 {g_val: j};
            if x * g_value == Self::group_one() {
                return g_value;
            }
        }
        assert!(false);
        return x;
    }

    // fn div(x: Self, y: Self) -> Self {
    //     Self::prod(x, Self::inv(y))
    // }
}
