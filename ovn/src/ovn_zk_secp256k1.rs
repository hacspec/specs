#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

pub use crate::ovn_zkgroup::*;
pub use group::{ff::Field, Group};

use hacspec_bip_340::{GroupTrait::*, Point, *};

impl MGroup for Point {
    fn hash(inp: Vec<Self>) -> Self::Scalar {
        return Self::Scalar::ONE; // TODO
    }
}

use bls12_381::*;

impl MGroup for Gt {
    fn hash(inp: Vec<Self>) -> Self::Scalar {
        return Self::Scalar::ONE; // TODO
    }
}
// hacspec_concordium::Serial + hacspec_concordium::Deserial,
