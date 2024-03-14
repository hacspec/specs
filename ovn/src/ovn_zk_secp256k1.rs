#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

pub use group::{ff::Field, Group};
pub use crate::ovn_zkgroup::*;

use hacspec_bip_340::{GroupTrait::*, Point, *};


impl MGroup for Point {
    fn pow (p: Self,exp: Self::Scalar) -> Self {
        point_mul(exp,p)
    }

    fn hash(inp: Vec<Self>) -> Self::Scalar {
        return Self::Scalar::ONE // TODO
    }

}

use bls12_381::*;

impl MGroup for Gt {
    fn pow (p: Self,exp: Self::Scalar) -> Self {
        p * exp
    }

    fn hash(inp: Vec<Self>) -> Self::Scalar {
        return Self::Scalar::ONE // TODO
    }

}
