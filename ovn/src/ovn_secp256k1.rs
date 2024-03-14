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

use hacspec_lib::*;

////////////////////////
// Impl for Secp256k1 //
////////////////////////

use hacspec_bip_340::*;

#[derive(core::marker::Copy, Clone, PartialEq, Eq)]
pub struct Z_curve {
    val: Scalar,
}

impl hacspec_concordium::Deserial for Z_curve {
    // TODO:
    fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
        let buffer: &mut [u8] = &mut [];
        let _ = _source.read(buffer)?;

        Ok(Z_curve {
            val: Scalar::from_public_byte_seq_be(Seq::<u8>::from_native_slice(buffer)),
        })
    }
}

impl hacspec_concordium::Serial for Z_curve {
    // TODO:
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        let _ = _out.write(self.val.to_public_byte_seq_be().native_slice());
        Ok(())
    }
}

impl Z_Field for Z_curve {
    type field_type = Z_curve;

    fn q() -> Self::field_type {
        Z_curve {
            val: Scalar::from_hex(
                "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            ),
        } // TODO: Scalar::modulo_value;
    }

    fn random_field_elem(random: u32) -> Self::field_type {
        Z_curve {
            val: Scalar::from_literal(random as u128),
        }
    }

    fn field_zero() -> Self::field_type {
        Z_curve {
            val: Scalar::from_literal(0u128),
        } // Scalar::ZERO()
    }

    fn field_one() -> Self::field_type {
        Z_curve {
            val: Scalar::from_literal(1u128),
        } // Scalar::ONE()
    }

    fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        Z_curve { val: x.val + y.val }
    }

    fn sub(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        Z_curve { val: x.val - y.val }
    }

    fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        Z_curve { val: x.val * y.val }
    }
}

#[derive(core::marker::Copy, Clone, PartialEq, Eq)]
pub struct Group_curve {
    val: Point,
}

impl hacspec_concordium::Deserial for Group_curve {
    // TODO:
    fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
        let buffer: &mut [u8] = &mut [];
        let _ = _source.read(buffer)?;
        if let [0] = buffer {
            return Ok(Group_curve {
                val: Point::AtInfinity,
            });
        }

        let buffer_y: &mut [u8] = &mut [];
        let _ = _source.read(buffer_y)?;

        Ok(Group_curve {
            val: Point::Affine((
                FieldElement::from_public_byte_seq_be(Seq::<u8>::from_native_slice(buffer)),
                FieldElement::from_public_byte_seq_be(Seq::<u8>::from_native_slice(buffer_y)),
            )),
        })
    }
}

impl hacspec_concordium::Serial for Group_curve {
    // TODO:
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        match self.val {
            Point::Affine(p) => {
                _out.write(x(p).to_public_byte_seq_be().native_slice());
                _out.write(y(p).to_public_byte_seq_be().native_slice())
            }
            Point::AtInfinity => _out.write(&[0]),
        };
        Ok(())
    }
}

impl Group<Z_curve> for Group_curve {
    type group_type = Group_curve;

    // https://eips.ethereum.org/EIPS/eip-2333
    fn g() -> Self::group_type {
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
            val: Point::Affine((
                FieldElement::from_public_byte_seq_be(gx),
                FieldElement::from_public_byte_seq_be(gy),
            )),
        }
    } // TODO

    fn pow(g: Self::group_type, x: <Z_curve as Z_Field>::field_type) -> Self::group_type {
        Group_curve {
            val: point_mul(x.val, g.val),
        }
    }

    fn g_pow(x: <Z_curve as Z_Field>::field_type) -> Self::group_type {
        Group_curve {
            val: point_mul_base(x.val),
        }
        // Self::pow(Self::g(), x)
    }

    fn group_one() -> Self::group_type {
        Self::g_pow(<Z_curve as Z_Field>::field_zero())
    }

    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        Group_curve {
            val: point_add(x.val, y.val),
        }
    }

    fn inv(x: Self::group_type) -> Self::group_type {
        Group_curve {
            val: match x.val {
                Point::Affine((a, b)) => Point::Affine((a, FieldElement::from_literal(0u128) - b)),
                Point::AtInfinity => Point::AtInfinity, // TODO?
            },
        }
    }

    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        Self::prod(x, Self::inv(y))
    }

    fn hash(x: Vec<Self::group_type>) -> <Z_curve as Z_Field>::field_type {
        // fp_hash_to_field
        Z_curve::field_one() // TODO: bls12-381 hash to curve?
    }
}
