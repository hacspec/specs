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

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

#[cfg(test)]
use rand::random;

extern crate hacspec_lib;
use hacspec_lib::*;

////////////////////
// Impl for Z/89Z //
////////////////////

pub use hacspec_ovn::*;
// pub use ovn_group::*;
// pub use ovn_trait::*;

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

////////////////////////
// Impl for Secp256k1 //
////////////////////////

use hacspec_bip_340::*;

#[derive(core::marker::Copy, Clone, PartialEq, Eq)]
struct Z_curve {
    val: Scalar,
}

impl hacspec_concordium::Deserial for Z_curve {
    // TODO:
    fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
        let buffer : &mut [u8] = &mut [];
        let _ = _source.read(buffer)?;
        
        Ok(Z_curve {
            val: Scalar::from_public_byte_seq_be(Seq::<u8>::from_native_slice(buffer)),
        })
    }
}

impl hacspec_concordium::Serial for Z_curve {
    // TODO:
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        _out.write(self.val.to_public_byte_seq_be().native_slice());
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
struct Group_curve {
    val: Point,
}

impl hacspec_concordium::Deserial for Group_curve {
    // TODO:
    fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
        let buffer : &mut [u8] = &mut [];
        let _ = _source.read(buffer)?;
        if let [0] = buffer {
            return Ok(Group_curve { val: Point::AtInfinity })
        }

        let buffer_y : &mut [u8] = &mut [];
        let _ = _source.read(buffer_y)?;

        Ok(Group_curve {
            val: Point::Affine((FieldElement::from_public_byte_seq_be(Seq::<u8>::from_native_slice(buffer)),
                                FieldElement::from_public_byte_seq_be(Seq::<u8>::from_native_slice(buffer_y)))),
        })
    }
}

impl hacspec_concordium::Serial for Group_curve {
    // TODO:
    fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        match self.val {
            Point::Affine(p) =>
            {
                _out.write(x(p).to_public_byte_seq_be().native_slice());
                _out.write(y(p).to_public_byte_seq_be().native_slice())
            },
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
                Point::Affine((a,b)) => Point::Affine((a, FieldElement::from_literal(0u128)-b)),
                Point::AtInfinity => Point::AtInfinity, // TODO?
            }
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


#[test]
pub fn schorr_zkp_correctness() {
    fn test(random_x: u32, random_r: u32) -> bool {
        type Z = z_89;
        type G = g_z_89;

        let x: u32 = Z::random_field_elem(random_x);
        let pow_x = G::g_pow(x);

        let pi: SchnorrZKPCommit<Z, G> = schnorr_zkp(random_r, pow_x, x);

        let valid = schnorr_zkp_validate::<Z, G>(pow_x, pi);
        valid
    }

    QuickCheck::new()
        .tests(10000)
        .quickcheck(test as fn(u32, u32) -> bool)
}

#[test]
pub fn schorr_zkp_secp256k1_correctness() {
    fn test(random_x: u32, random_r: u32) -> bool {
        type Z = Z_curve;
        type G = Group_curve;

        let x: Z_curve = Z::random_field_elem(random_x);
        let pow_x = G::g_pow(x);

        let pi: SchnorrZKPCommit<Z, G> = schnorr_zkp(random_r, pow_x, x);

        let valid = schnorr_zkp_validate::<Z, G>(pow_x, pi);
        valid
    }

    QuickCheck::new()
        .tests(10)
        .quickcheck(test as fn(u32, u32) -> bool)
}

#[cfg(test)]
pub fn or_zkp_correctness<Z : Z_Field, G : Group<Z>>(
        random_w: u32,
        random_r: u32,
        random_d: u32,
        random_h: u32,
        random_x: u32,
        v: bool,
) -> bool {
    let mut h = G::g_pow(Z::random_field_elem(random_h));
    let x = Z::random_field_elem(random_x);
    let pi: OrZKPCommit<Z, G> = zkp_one_out_of_two(random_w, random_r, random_d, h, x, v);
    let valid = zkp_one_out_of_two_validate::<Z, G>(h, pi);
    valid
}

#[test]
pub fn or_zkp_correctness_z89(){
    QuickCheck::new()
        .tests(10000)
        .quickcheck(or_zkp_correctness::<z_89, g_z_89> as fn(u32, u32, u32, u32, u32, bool) -> bool)
}

#[test]
// TODO: Fix inverse opeation, should make this test parse
pub fn or_zkp_secp256k1_correctness() {
    QuickCheck::new()
        .tests(10)
        .quickcheck(or_zkp_correctness::<Z_curve, Group_curve> as fn(u32, u32, u32, u32, u32, bool) -> bool)
}

#[cfg(test)]
pub fn sum_to_zero<Z: Z_Field, G: Group<Z>, const n: usize>() {
    let mut xis: [Z::field_type; n] = [Z::field_zero(); n];
    let mut g_pow_xis: [G::group_type; n] = [G::group_one(); n];
    use rand::random;
    for i in 0..n {
        xis[i] = Z::random_field_elem(random());
        g_pow_xis[i] = G::g_pow(xis[i]);
    }

    let mut res = G::group_one();
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<Z, G, n>(i, g_pow_xis);
        res = G::prod(res, G::pow(g_pow_yi, xis[i]));
    }

    assert!(res == G::group_one());
}

#[test]
pub fn sum_to_zero_z89() {
    sum_to_zero::<z_89, g_z_89, 55>()
}

#[test]
pub fn sum_to_zero_secp256k1() {
    sum_to_zero::<Z_curve, Group_curve, 55>()
}

#[cfg(test)]
pub fn test_correctness<Z: Z_Field, G: Group<Z>, const n: usize, A: HasActions>(
    votes: [bool; n],
    xis: [Z::field_type; n],
    rp_zkp_randoms: [u32; n],
    cvp_zkp_random_ws1: [u32; n],
    cvp_zkp_random_rs1: [u32; n],
    cvp_zkp_random_ds1: [u32; n],
    cvp_zkp_random_ws2: [u32; n],
    cvp_zkp_random_rs2: [u32; n],
    cvp_zkp_random_ds2: [u32; n],
) -> bool {
    // Setup the context
    let mut ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();

    let mut state: OvnContractState<Z, G, n> = init_ovn_contract().unwrap();

    for i in 0..n {
        let parameter = RegisterParam::<Z> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            register_vote::<Z, G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws1[i],
            cvp_zkp_random_r: cvp_zkp_random_rs1[i],
            cvp_zkp_random_d: cvp_zkp_random_ds1[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            commit_to_vote::<Z, G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            cast_vote::<Z, G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state).unwrap();
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx = ctx.set_parameter(&parameter_bytes);

    (_, state) = tally_votes::<Z, G, n, A>(ctx.clone(), state).unwrap();

    let mut count = 0u32;
    for v in votes {
        if v {
            count = count + 1; // += 1 does not work correctly
        }
    }

    assert_eq!(state.tally, count);
    state.tally == count
}

#[cfg(test)]
fn randomized_full_test<Z: Z_Field, G: Group<Z>, const n: usize> () -> bool {
    use rand::random;
    let mut votes: [bool; n] = [false; n];
    let mut xis: [Z::field_type; n] = [Z::field_zero(); n];
    let mut rp_zkp_randoms: [u32; n] = [0; n];
    let mut cvp_zkp_random_ws1: [u32; n] = [0; n];
    let mut cvp_zkp_random_rs1: [u32; n] = [0; n];
    let mut cvp_zkp_random_ds1: [u32; n] = [0; n];

    let mut cvp_zkp_random_ws2: [u32; n] = [0; n];
    let mut cvp_zkp_random_rs2: [u32; n] = [0; n];
    let mut cvp_zkp_random_ds2: [u32; n] = [0; n];

    for i in 0..n {
        votes[i] = random();
        xis[i] = Z::random_field_elem(random());
        rp_zkp_randoms[i] = random();
        cvp_zkp_random_ws1[i] = random();
        cvp_zkp_random_rs1[i] = random();
        cvp_zkp_random_ds1[i] = random();
        cvp_zkp_random_ws2[i] = random();
        cvp_zkp_random_rs2[i] = random();
        cvp_zkp_random_ds2[i] = random();
    }

    test_correctness::<Z, G, n, hacspec_concordium::test_infrastructure::ActionsTree>(
        votes,
        xis,
        rp_zkp_randoms,
        cvp_zkp_random_ws1,
        cvp_zkp_random_rs1,
        cvp_zkp_random_ds1,
        cvp_zkp_random_ws2,
        cvp_zkp_random_rs2,
        cvp_zkp_random_ds2,
    )
}

// #[concordium_test]
#[test]
fn test_full_z89() {
    QuickCheck::new()
        .tests(100)
        .quickcheck(randomized_full_test::<z_89, g_z_89, 55> as fn() -> bool)
}

// #[concordium_test]
#[test]
fn test_full_secp256k1() {
    QuickCheck::new()
        .tests(1)
        .quickcheck(randomized_full_test::<Z_curve, Group_curve, 15> as fn() -> bool)
}
