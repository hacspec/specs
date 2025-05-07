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

use hacspec_lib::*;

////////////////////////
// Impl for Secp256k1 //
////////////////////////

use hacspec_bip_340::*;

#[derive(core::marker::Copy, Clone, PartialEq, Eq)]
pub struct Z_curve {
    z_val: Scalar,
}

impl hacspec_concordium::Deserial for Z_curve {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let temp : Vec<u8> = source.get()?;

        Ok(Z_curve {
            z_val: Scalar::from_public_byte_seq_be(Seq::<u8>::from_vec(temp)),
        })
    }
}

impl hacspec_concordium::Serial for Z_curve {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        let mut v : Vec<u8> = Vec::new();
        for x in self.z_val.to_public_byte_seq_be().native_slice() {
            v.push(x.clone());
        }
        v.serial(out)
    }
}

impl core::ops::Mul for Z_curve {
    type Output = Self;
    fn mul(self, y: Self) -> Self {
        Z_curve { z_val: self.z_val * y.z_val }
    }
}

impl core::iter::Product for Z_curve {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            Z_curve {
                z_val: Scalar::from_literal(1u128),
            },
            |a, b| a * b,
        )
    }
}

impl core::ops::Add for Z_curve {
    type Output = Self;
    fn add(self, y: Self) -> Self {
        Z_curve { z_val: self.z_val + y.z_val }
    }
}

impl core::ops::Neg for Z_curve {
    type Output = Self;
    fn neg(self) -> Self {
        Z_curve { z_val: Self::field_zero().z_val - self.z_val }
    }
}

impl Field for Z_curve {
    fn q() -> Self {
        Z_curve {
            z_val: Scalar::from_hex(
                "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            ),
        }
    }

    fn random_field_elem(random: u32) -> Self {
        Z_curve {
            z_val: Scalar::from_literal(random as u128),
        }
    }

    fn field_zero() -> Self {
        Z_curve {
            z_val: Scalar::from_literal(0u128),
        } // Scalar::ZERO()
    }

    fn field_one() -> Self {
        Z_curve {
            z_val: Scalar::from_literal(1u128),
        } // Scalar::ONE()
    }

    // fn sub(x: Self, y: Self) -> Self {
    //     Z_curve { z_val: x.z_val - y.z_val }
    // }

    fn inv(x: Self) -> Self {
        assert!(false); // Missing
        return x;
    }

}


#[derive(core::marker::Copy, Clone, PartialEq, Eq)]
pub struct Group_curve {
    g_val: Point,
}

impl hacspec_concordium::Deserial for Group_curve {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let b : bool = source.get()?;
        if b {
            let vx : Vec<u8> = source.get()?;
            let vy : Vec<u8> = source.get()?;

            Ok(Group_curve {
                g_val: Point::Affine((
                    FieldElement::from_public_byte_seq_be(Seq::<u8>::from_vec(vx)),
                    FieldElement::from_public_byte_seq_be(Seq::<u8>::from_vec(vy)),
                )),
            })
        } else {
            Ok(Group_curve { g_val: Point::AtInfinity })
        }
    }
}

impl hacspec_concordium::Serial for Group_curve {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self.g_val {
            Point::Affine(p) => {
                true.serial(out)?;

                let mut vx : Vec<u8> = Vec::new();
                for x in x(p).to_public_byte_seq_be().native_slice() {
                    vx.push(x.clone());
                }
                let _ = vx.serial(out)?;

                let mut vy : Vec<u8> = Vec::new();
                for y in y(p).to_public_byte_seq_be().native_slice() {
                    vy.push(y.clone());
                }
                let _ = vy.serial(out)?;
            }
            Point::AtInfinity => {
                let _ = false.serial(out)?;
            },
        };
        Ok(())
    }
}

impl core::ops::Mul for Group_curve {
    type Output = Self;
    fn mul(self, y: Self) -> Self {
        Group_curve {
            g_val: point_add(self.g_val, y.g_val),
        }
    }
}

impl core::iter::Product for Group_curve {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            Self::g_pow(<Z_curve as Field>::field_zero()),
            |a, b| a * b,
        )
    }
}

impl Group for Group_curve {
    type Z = Z_curve;

    // https://eips.ethereum.org/EIPS/eip-2333
    fn g() -> Self {
        #[rustfmt::skip]
        let gx = PBytes32([
            0x79u8, 0xBEu8, 0x66u8, 0x7Eu8, 0xF9u8, 0xDCu8, 0xBBu8, 0xACu8,
            0x55u8, 0xA0u8, 0x62u8, 0x95u8, 0xCEu8, 0x87u8, 0x0Bu8, 0x07u8,
            0x02u8, 0x9Bu8, 0xFCu8, 0xDBu8, 0x2Du8, 0xCEu8, 0x28u8, 0xD9u8,
            0x59u8, 0xF2u8, 0x81u8, 0x5Bu8, 0x16u8, 0xF8u8, 0x17u8, 0x98u8
        ]);
        #[rustfmt::skip]
        let gy = PBytes32([
            0x48u8, 0x3Au8, 0xDAu8, 0x77u8, 0x26u8, 0xA3u8, 0xC4u8, 0x65u8,
            0x5Du8, 0xA4u8, 0xFBu8, 0xFCu8, 0x0Eu8, 0x11u8, 0x08u8, 0xA8u8,
            0xFDu8, 0x17u8, 0xB4u8, 0x48u8, 0xA6u8, 0x85u8, 0x54u8, 0x19u8,
            0x9Cu8, 0x47u8, 0xD0u8, 0x8Fu8, 0xFBu8, 0x10u8, 0xD4u8, 0xB8u8
        ]);
        Group_curve {
            g_val: Point::Affine((
                FieldElement::from_public_byte_seq_be(gx),
                FieldElement::from_public_byte_seq_be(gy),
            )),
        }
    }

    fn pow(g: Self, x: Z_curve) -> Self {
        Group_curve {
            g_val: point_mul(x.z_val, g.g_val),
        }
    }

    fn g_pow(x: Z_curve) -> Self {
        Group_curve {
            g_val: point_mul_base(x.z_val),
        }
        // Self::pow(Self::g(), x)
    }

    fn group_one() -> Self {
        Self::g_pow(<Z_curve as Field>::field_zero())
    }

    fn group_inv(x: Self) -> Self {
        Group_curve {
            g_val: match x.g_val {
                Point::Affine((a, b)) => Point::Affine((a, FieldElement::from_literal(0u128) - b)),
                Point::AtInfinity => Point::AtInfinity,
            },
        }
    }

    // fn div(x: Self, y: Self) -> Self {
    //     Self::prod(x, Self::inv(y))
    // }

    fn hash(x: Vec<Self>) -> Z_curve {
        // fp_hash_to_field
        Z_curve::field_one() // TODO: bls12-381 hash to curve?
    }
}
