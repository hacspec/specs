#![no_std]
#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;

#[hax_lib_macros::exclude]
use hax_lib_macros::*;

// #[exclude]
use hacspec_concordium::*;
// #[exclude]
use hacspec_concordium_derive::*;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

pub use hacspec_ovn::ovn_group::*;
pub use hacspec_ovn::ovn_secp256k1::*;
pub use hacspec_ovn::ovn_z_89::*;

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
pub fn or_zkp_correctness<Z: Z_Field, G: Group<Z>>(
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
pub fn or_zkp_correctness_z89() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(or_zkp_correctness::<z_89, g_z_89> as fn(u32, u32, u32, u32, u32, bool) -> bool)
}

#[test]
// TODO: Fix inverse opeation, should make this test parse
pub fn or_zkp_secp256k1_correctness() {
    QuickCheck::new().tests(10).quickcheck(
        or_zkp_correctness::<Z_curve, Group_curve> as fn(u32, u32, u32, u32, u32, bool) -> bool,
    )
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
fn randomized_full_test<Z: Z_Field, G: Group<Z>, const n: usize>() -> bool {
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

// // #[concordium_test]
// #[test]
// fn test_full_secp256k1() {
//     QuickCheck::new()
//         .tests(1)
//         .quickcheck(randomized_full_test::<Z_curve, Group_curve, 15> as fn() -> bool)
// }
