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

#[cfg(test)]
pub fn schnorr_zkp_correctness<G: Group>(random_x: u32, random_r: u32) -> bool {
    let x: G::Z = G::Z::random_field_elem(random_x);
    let r: G::Z = G::Z::random_field_elem(random_r);

    let pow_x = G::g_pow(x);

    let pi: SchnorrZKPCommit<G> = schnorr_zkp(r, pow_x, x);

    let valid = schnorr_zkp_validate::<G>(pow_x, pi);
    valid
}

#[test]
pub fn schnorr_zkp_z_89_correctness() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(schnorr_zkp_correctness::<g_z_89> as fn(u32, u32) -> bool)
}

#[test]
pub fn schorr_zkp_secp256k1_correctness() {
    QuickCheck::new()
        .tests(10)
        .quickcheck(schnorr_zkp_correctness::<Group_curve> as fn(u32, u32) -> bool)
}

#[cfg(test)]
pub fn or_zkp_correctness<G: Group>(
    random_w: u32,
    random_r: u32,
    random_d: u32,
    random_h: u32,
    random_x: u32,
    v: bool,
) -> bool {
    let w = G::Z::random_field_elem(random_w);
    let r = G::Z::random_field_elem(random_r);
    let d = G::Z::random_field_elem(random_d);
    let h = G::Z::random_field_elem(random_h);
    let x = G::Z::random_field_elem(random_x);

    let mut h = G::g_pow(h);
    let x = x;
    let pi: OrZKPCommit<G> = zkp_one_out_of_two(w, r, d, h, x, v);
    let valid = zkp_one_out_of_two_validate::<G>(h, pi);
    valid
}

#[test]
pub fn or_zkp_correctness_z89() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(or_zkp_correctness::<g_z_89> as fn(u32, u32, u32, u32, u32, bool) -> bool)
}

#[test]
// TODO: Fix inverse opeation, should make this test parse
pub fn or_zkp_secp256k1_correctness() {
    QuickCheck::new().tests(10).quickcheck(
        or_zkp_correctness::<Group_curve> as fn(u32, u32, u32, u32, u32, bool) -> bool,
    )
}

#[cfg(test)]
pub fn sum_to_zero<G: Group, const n: usize>() {
    let mut xis: [G::Z; n] = [G::Z::field_zero(); n];
    let mut g_pow_xis: [G; n] = [G::group_one(); n];
    use rand::random;
    for i in 0..n {
        xis[i] = G::Z::random_field_elem(random());
        g_pow_xis[i] = G::g_pow(xis[i]);
    }

    let mut res = G::group_one();
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<G, n>(i, g_pow_xis);
        res = (res * /* group product */  G::pow(g_pow_yi, xis[i]));
    }

    assert!(res == G::group_one());
}

#[test]
pub fn sum_to_zero_z89() {
    sum_to_zero::<g_z_89, 55>()
}

#[test]
pub fn sum_to_zero_secp256k1() {
    sum_to_zero::<Group_curve, 55>()
}

use rand::random;


#[derive(Copy, Clone, hacspec_concordium::Serial, hacspec_concordium::Deserial)]
pub struct ElemOfEach<G : Group> {
    i : u32,
    z : G::Z,
    g : G,
}

#[cfg(test)]
pub fn test_params_of_group<
    G: Group,
    A: HasActions,
    >() {
    // Setup the context
    let mut ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();
    let parameter = ElemOfEach::<G> {
        i: random(),
        z: G::Z::random_field_elem(random()),
        g: G::g_pow(G::Z::random_field_elem(random())),
    };
    let parameter_bytes = to_bytes(&parameter);
    let ctx_params = ctx.clone().set_parameter(&parameter_bytes);
    let param_back: Result<ElemOfEach<G>, ParseError> =
        ctx_params.parameter_cursor().get();
    assert!(param_back.is_ok());

    let wu_param = param_back.unwrap();
    assert!(wu_param.i == parameter.i);
    assert!(wu_param.z == parameter.z);
    assert!(wu_param.g == parameter.g);
}

#[test]
pub fn test_params_of_group_z89() {
    test_params_of_group::<g_z_89, hacspec_concordium::test_infrastructure::ActionsTree>()
}

#[test]
pub fn test_params_of_group_secp256k1() {
    test_params_of_group::<Group_curve, hacspec_concordium::test_infrastructure::ActionsTree>()
}

#[cfg(test)]
pub fn test_correctness<G: Group, const n: usize, A: HasActions>(
    votes: [bool; n],
    xis: [G::Z; n],
    rp_zkp_randoms: [G::Z; n],
    cvp_zkp_random_ws1: [G::Z; n],
    cvp_zkp_random_rs1: [G::Z; n],
    cvp_zkp_random_ds1: [G::Z; n],
    cvp_zkp_random_ws2: [G::Z; n],
    cvp_zkp_random_rs2: [G::Z; n],
    cvp_zkp_random_ds2: [G::Z; n],
) -> bool {
    // Setup the context
    let mut ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();

    let mut state: OvnContractState<G, n> = init_ovn_contract().unwrap();

    for i in 0..n {
        let parameter = RegisterParam::<G::Z> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            register_vote::<G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws1[i],
            cvp_zkp_random_r: cvp_zkp_random_rs1[i],
            cvp_zkp_random_d: cvp_zkp_random_ds1[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            commit_to_vote::<G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            cast_vote::<G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state).unwrap();
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx = ctx.set_parameter(&parameter_bytes);

    (_, state) = tally_votes::<G, n, A>(ctx.clone(), state).unwrap();

    let mut count = 0u32;
    for v in votes {
        if v {
            count = count + 1;
        }
    }

    assert_eq!(state.tally, count);
    state.tally == count
}

#[cfg(test)]
fn randomized_full_test<G: Group, const n: usize>() -> bool {
    use rand::random;
    let mut votes: [bool; n] = [false; n];
    let mut xis: [G::Z; n] = [G::Z::field_zero(); n];
    let mut rp_zkp_randoms: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ws1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds1: [G::Z; n] = [G::Z::field_zero(); n];

    let mut cvp_zkp_random_ws2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds2: [G::Z; n] = [G::Z::field_zero(); n];

    for i in 0..n {
        votes[i] = random();
        xis[i] = G::Z::random_field_elem(random());
        rp_zkp_randoms[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds2[i] = G::Z::random_field_elem(random());
    }

    test_correctness::<G, n, hacspec_concordium::test_infrastructure::ActionsTree>(
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
        .quickcheck(randomized_full_test::<g_z_89, 55> as fn() -> bool)
}

// #[concordium_test]
#[test]
fn test_full_secp256k1() {
    QuickCheck::new()
        .tests(1)
        .quickcheck(randomized_full_test::<Group_curve, 15> as fn() -> bool)
}
