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

pub use bls12_381::{Scalar as BlsScalar, *};
use core::marker::PhantomData;
pub use group::{ff::Field, Group};
pub use hacspec_ovn::{ovn_zk_secp256k1::*, ovn_zkgroup::*};

use rand_core::{RngCore, *};
// use quickcheck::RngCore;
use hacspec_bip_340::{GroupTrait::*, Point, Scalar as BipScalar, *};

use rand::random;
use rand::rngs::StdRng;

#[derive(Serialize)]
struct GroupBits<const n: usize> {
    val: [u8; n],
}

impl From<BlsScalar> for GroupBits<32> {
    fn from(value: BlsScalar) -> Self {
        Self {
            val: value.to_bytes(),
        }
    }
}

impl Into<BlsScalar> for GroupBits<32> {
    fn into(self) -> BlsScalar {
        BlsScalar::from_bytes(&self.val).unwrap()
    }
}

impl From<BipScalar> for GroupBits<32> {
    fn from(value: BipScalar) -> Self {
        let mut val: [u8; 32] = [0u8; 32];
        let temp = value.to_be_bytes();
        for i in 0..32 {
            val[i] = temp[i];
        }
        Self { val }
    }
}

impl Into<BipScalar> for GroupBits<32> {
    fn into(self) -> BipScalar {
        BipScalar::from_be_bytes(&self.val)
    }
}

////////////////////////////
// Group operations tests //
////////////////////////////

#[cfg(test)]
pub fn group_test<G: MGroup>() {
    let r: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let x: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    assert_eq!(
        G::generator() * (r + x),
        (G::generator() * r + G::generator() * (x)),
        "!!temp aa!!"
    );
}

#[test]
pub fn secp256k1_group_correctness() {
    group_test::<Point>()
}

#[test]
pub fn bls12_381_real_group_correctness() {
    group_test::<Gt>()
}

#[cfg(test)]
pub fn schnorr_zkp_correctness<G: MGroup>() -> bool {
    let random_r: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let x: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let pow_x = G::generator() * x; // G::g_pow(x);

    let pi: SchnorrZKPCommit<G> = schnorr_zkp(random_r, pow_x, x);

    let valid = schnorr_zkp_validate::<G>(pow_x, pi);
    valid
}

#[test]
pub fn schnorr_zkp_secp256k1_correctness() {
    assert!(schnorr_zkp_correctness::<Point>())
    // QuickCheck::new()
    //     .tests(1000)
    //     .quickcheck(schnorr_zkp_correctness::<Point> as fn() -> bool)
}

#[test]
pub fn schnorr_correctness_bls12_381_real() {
    assert!(schnorr_zkp_correctness::<Gt>())
}

#[cfg(test)]
pub fn or_zkp_correctness<G: MGroup>(v: bool) -> bool {
    let random_w: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let random_r: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let random_d: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let random_h: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let random_x: <G as Group>::Scalar = <G as Group>::Scalar::random(rand::thread_rng());
    let mut h = G::g_pow(random_h);
    let x = random_x;
    let pi: OrZKPCommit<G> = zkp_one_out_of_two(random_w, random_r, random_d, h, x, v);
    let valid = zkp_one_out_of_two_validate::<G>(h, pi);
    valid
}

#[test]
// TODO: Fix inverse opeation, should make this test parse
pub fn or_zkp_secp256k1() {
    QuickCheck::new()
        .tests(10)
        .quickcheck(or_zkp_correctness::<Point> as fn(bool) -> bool)
}

#[test]
pub fn or_zkp_bls12_381_real() {
    QuickCheck::new()
        .tests(10)
        .quickcheck(or_zkp_correctness::<Gt> as fn(bool) -> bool)
}

#[cfg(test)]
pub fn sum_to_zero<G: MGroup, const n: usize>() {
    let mut xis: [G::Scalar; n] = [G::Scalar::ZERO; n];
    let mut g_pow_xis: [G; n] = [G::identity(); n];
    use rand::random;
    for i in 0..n {
        xis[i] = G::Scalar::random(rand::thread_rng());
        g_pow_xis[i] = G::g_pow(xis[i]);
    }

    let mut res = G::identity();
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<G, n>(i, g_pow_xis);
        res = res + G::pow(g_pow_yi, xis[i]);
    }

    assert!(res == G::identity());
}

#[test]
pub fn sum_to_zero_secp256k1() {
    sum_to_zero::<Point, 55>()
}

#[test]
pub fn sum_to_zero_bls12_381_real() {
    sum_to_zero::<Gt, 55>()
}

#[cfg(test)]
pub fn test_params_of_group<
    G: MGroup,
    S: Serialize + From<G::Scalar> + Into<G::Scalar>,
    A: HasActions,
>() {
    // Setup the context
    let mut ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();
    let parameter = RegisterParam::<G::Scalar, S> {
        rp_i: random(),
        rp_xi: G::Scalar::random(rand::thread_rng()),
        rp_zkp_random: G::Scalar::random(rand::thread_rng()),
        phantom: PhantomData,
    };
    let parameter_bytes = to_bytes(&parameter);
    let ctx_params = ctx.clone().set_parameter(&parameter_bytes);
    let param_back: Result<RegisterParam<G::Scalar, S>, ParseError> =
        ctx_params.parameter_cursor().get();
    assert!(param_back.is_ok());

    let wu_param = param_back.unwrap();
    assert_eq!(wu_param.rp_i, parameter.rp_i);
    assert_eq!(wu_param.rp_xi, parameter.rp_xi);
    assert_eq!(wu_param.rp_zkp_random, parameter.rp_zkp_random);
}

#[test]
pub fn test_params_of_group_zk259() {
    test_params_of_group::<Point, GroupBits<32>, hacspec_concordium::test_infrastructure::ActionsTree>(
    )
}

#[test]
pub fn test_params_of_group_bls12_381_real() {
    test_params_of_group::<Gt, GroupBits<32>, hacspec_concordium::test_infrastructure::ActionsTree>(
    )
}

#[cfg(test)]
pub fn test_correctness<
    G: MGroup,
    S: Serialize + From<G::Scalar> + Into<G::Scalar>,
    const n: usize,
    A: HasActions,
>(
    votes: [bool; n],
    xis: [G::Scalar; n],
    rp_zkp_randoms: [G::Scalar; n],
    cvp_zkp_random_ws1: [G::Scalar; n],
    cvp_zkp_random_rs1: [G::Scalar; n],
    cvp_zkp_random_ds1: [G::Scalar; n],
    cvp_zkp_random_ws2: [G::Scalar; n],
    cvp_zkp_random_rs2: [G::Scalar; n],
    cvp_zkp_random_ds2: [G::Scalar; n],
) -> bool {
    // Setup the context
    let ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();

    let mut state: OvnContractState<G, n> = init_ovn_contract().unwrap();

    for i in 0..n {
        let parameter = RegisterParam::<G::Scalar, S> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i],
            phantom: PhantomData,
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            register_vote::<G, S, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    assert!(false, "Got here 2");
    
    for i in 0..n {
        let parameter = CastVoteParam::<G::Scalar, S> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws1[i],
            cvp_zkp_random_r: cvp_zkp_random_rs1[i],
            cvp_zkp_random_d: cvp_zkp_random_ds1[i],
            cvp_vote: votes[i],
            phantom: PhantomData,
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            commit_to_vote::<G, S, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<G::Scalar, S> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
            phantom: PhantomData,
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            cast_vote::<G, S, n, A>(ctx.clone().set_parameter(&parameter_bytes), state).unwrap();
    }

    assert!(false, "Got here 3");

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);

    (_, state) =
        tally_votes::<G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state).unwrap();

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
fn randomized_full_test<
    G: MGroup,
    S: Serialize + From<G::Scalar> + Into<G::Scalar>,
    const n: usize,
>() -> bool {
    let mut votes: [bool; n] = [false; n];
    let mut xis: [G::Scalar; n] = [G::Scalar::ONE; n];
    let mut rp_zkp_randoms: [G::Scalar; n] = [G::Scalar::ONE; n];
    let mut cvp_zkp_random_ws1: [G::Scalar; n] = [G::Scalar::ONE; n];
    let mut cvp_zkp_random_rs1: [G::Scalar; n] = [G::Scalar::ONE; n];
    let mut cvp_zkp_random_ds1: [G::Scalar; n] = [G::Scalar::ONE; n];

    let mut cvp_zkp_random_ws2: [G::Scalar; n] = [G::Scalar::ONE; n];
    let mut cvp_zkp_random_rs2: [G::Scalar; n] = [G::Scalar::ONE; n];
    let mut cvp_zkp_random_ds2: [G::Scalar; n] = [G::Scalar::ONE; n];

    for i in 0..n {
        votes[i] = random();
        xis[i] = G::Scalar::random(rand::thread_rng());
        rp_zkp_randoms[i] = G::Scalar::random(rand::thread_rng());
        cvp_zkp_random_ws1[i] = G::Scalar::random(rand::thread_rng());
        cvp_zkp_random_rs1[i] = G::Scalar::random(rand::thread_rng());
        cvp_zkp_random_ds1[i] = G::Scalar::random(rand::thread_rng());
        cvp_zkp_random_ws2[i] = G::Scalar::random(rand::thread_rng());
        cvp_zkp_random_rs2[i] = G::Scalar::random(rand::thread_rng());
        cvp_zkp_random_ds2[i] = G::Scalar::random(rand::thread_rng());
    }

    test_correctness::<G, S, n, hacspec_concordium::test_infrastructure::ActionsTree>(
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

#[test]
fn test_full_secp256k1() {
    QuickCheck::new()
        .tests(1)
        .quickcheck(randomized_full_test::<Point, GroupBits<32>, 15> as fn() -> bool)
}

#[test]
fn test_full_bls12_381_real() {
    QuickCheck::new()
        .tests(1)
        .quickcheck(randomized_full_test::<Gt, GroupBits<32>, 15> as fn() -> bool)
}
