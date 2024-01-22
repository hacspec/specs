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

use hacspec_bls12_381::*;

pub trait Z_Field : core::marker::Copy {
    type field_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

    const q : usize;

    fn random_field_elem(random : u32) -> Self::field_type;

    fn field_zero() -> Self::field_type;
    fn field_one() -> Self::field_type;

    fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type;
    fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type;
}

/** Interface for group implementation */
pub trait Group<Z: Z_Field> : core::marker::Copy {
    type group_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

    const g: Self::group_type; // Generator (elemnent of group)

    fn random_group_elem(random : u32) -> Self::group_type;

    fn g_pow(x: Z::field_type) -> Self::group_type;
    fn pow(g: Self::group_type, x: Z::field_type) -> Self::group_type; // TODO: Link with q
    fn group_one() -> Self::group_type;
    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type;
    fn inv(x: Self::group_type) -> Self::group_type;
    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type;
}

// struct eligible_votes {
//     v_id : u32,
// }

// /** number of parties */
// const n : u32 = 3u32;
// const P : [eligible_votes; 3] = // n = 3
//     [eligible_votes {v_id: 0},
//      eligible_votes {v_id: 1},
//      eligible_votes {v_id: 2}];

// use concordium_contracts_common::*;
// extern crate concordium_std;

// use hacspec_sha256::*;

/** TODO: Hash function */
pub fn Hash<Z : Z_Field, G : Group<Z>>(v : (G::group_type, G::group_type, G::group_type)) -> Z::field_type {
    let (a, b, c) = v;
    Z::field_one()
}

#[derive(Serialize, SchemaType, Clone, Copy)]
struct SchnorrZKPCommit<Z : Z_Field, G: Group<Z>> {
    u: G::group_type,
    c: Z::field_type,
    z: Z::field_type,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics */
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_ZKP<Z : Z_Field, G: Group<Z>>(random: u32, g_pow_x: G::group_type, x: Z::field_type) -> SchnorrZKPCommit<Z, G> {
    let r = Z::random_field_elem(random);
    let u = G::g_pow(r);
    let c = Hash::<Z,G>((G::g, g_pow_x, u));
    let z = Z::add(r , Z::mul(c , x) );

    return SchnorrZKPCommit { u, c, z };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_ZKP_validate<Z : Z_Field, G: Group<Z>>(g_pow_x: G::group_type, pi: SchnorrZKPCommit<Z, G>) -> bool {
    pi.c == Hash::<Z,G>((G::g, g_pow_x, pi.u)) && G::g_pow(pi.z) == G::prod(pi.u , G::pow(g_pow_x, pi.c))
}

#[hax::contract_state(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), contract_state(contract = "OVN"))]
#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OvnContractState<Z : Z_Field, G: Group<Z>, const n: usize> {
    zkp_random: u32,

    g_pow_xis: [G::group_type; n],
    zkp_xis: [SchnorrZKPCommit<Z, G>; n],

    commit_vis: [u32; n],

    g_pow_xi_yi_vis: [G::group_type; n],
    zkp_vis: [u32; n],

    tally: u32,
}

#[hax::init(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
pub fn init_ovn_contract<Z : Z_Field, G: Group<Z>, const n: usize>(
    _: &impl HasInitContext,
) -> InitResult<OvnContractState<Z,G,n>> {
    Ok(OvnContractState::<Z,G,n> {
        zkp_random: 0, // TODO

        g_pow_xis: [G::group_one(); n],
        zkp_xis: [SchnorrZKPCommit::<Z, G> { u: G::group_one(), z: Z::field_zero(), c: Z::field_zero() }; n],

        commit_vis: [0; n],

        g_pow_xi_yi_vis: [G::group_one(); n],
        zkp_vis: [0; n],

        tally: 0,
    })
}

/** Currently randomness needs to be injected */
pub fn select_private_voting_key<Z : Z_Field, G : Group<Z>>(random: u32) -> G::group_type {
    G::random_group_elem(random) // x_i \in_R Z_q;
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParam<Z : Z_Field> {
    rp_i: u32,
    rp_xi: Z::field_type,
}

/** Primary function in round 1 */
#[hax::receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "register", parameter = "RegisterParam"))]
pub fn register_vote<Z : Z_Field, G : Group<Z>, const n : usize, A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    let params: RegisterParam<Z> = ctx.parameter_cursor().get()?;
    let g_pow_xi = G::g_pow(params.rp_xi);

    let zkp_xi = schnorr_ZKP::<Z, G>(state.zkp_random, g_pow_xi, params.rp_xi);

    let mut register_vote_state_ret = state.clone();
    register_vote_state_ret.g_pow_xis[params.rp_i as usize] = g_pow_xi;
    register_vote_state_ret.zkp_xis[params.rp_i as usize] = zkp_xi;

    Ok((A::accept(), register_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParam<Z : Z_Field> {
    cvp_i: u32,
    cvp_xi: Z::field_type,
    cvp_vote: bool,
}

pub fn compute_group_element_for_vote<Z : Z_Field, G: Group<Z>, const n: usize>(
    i: u32,
    xi: Z::field_type,
    vote: bool,
    xis: [G::group_type; n],
) -> G::group_type {
    let mut prod1 = G::group_one();
    for j in 0..(i - 1) as usize {
        prod1 = G::prod(prod1, xis[j]);
    }
    let mut prod2 = G::group_one();
    for j in (i + 1) as usize..n {
        prod2 = G::prod(prod2, xis[j]);
    }
    let Yi = G::div(prod1, prod2);
    // implicityly: Y_i = g^y_i
    G::prod(G::pow(Yi, xi), G::g_pow(if vote { Z::field_one() } else { Z::field_zero() }))
}

pub fn commit_to<Z : Z_Field, G: Group<Z>>(x: G::group_type) -> u32 {
    0
}

/** Commitment before round 2 */
#[hax::receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam"))]
pub fn commit_to_vote<Z : Z_Field, G : Group<Z>, const n : usize, A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    let params: CastVoteParam<Z> = ctx.parameter_cursor().get()?;

    for i in 0..n {
        if !schnorr_ZKP_validate(state.g_pow_xis[i], state.zkp_xis[i]) {
            return Err(ParseError {});
        }
    }

    let g_pow_xi_yi_vi = compute_group_element_for_vote::<Z, G, n>(params.cvp_i, params.cvp_xi, params.cvp_vote, state.g_pow_xis);
    let commit_vi = commit_to::<Z, G>(g_pow_xi_yi_vi);

    let mut commit_to_vote_state_ret = state.clone();
    commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = commit_vi;
    Ok((A::accept(), commit_to_vote_state_ret))
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn ZKP_one_out_of_two<Z : Z_Field, G: Group<Z>>(g_pow_vi: G::group_type, vi: bool) -> u32 {
    32 // TODO
}

/** Primary function in round 2, also opens commitment */
#[hax::receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam"))]
pub fn cast_vote<Z : Z_Field, G : Group<Z>, const n : usize, A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    let params: CastVoteParam<Z> = ctx.parameter_cursor().get()?;

    let g_pow_xi_yi_vi = compute_group_element_for_vote::<Z, G, n>(params.cvp_i, params.cvp_xi, params.cvp_vote, state.g_pow_xis);
    let zkp_vi = ZKP_one_out_of_two::<Z, G>(g_pow_xi_yi_vi, params.cvp_vote);

    let mut cast_vote_state_ret = state.clone();
    cast_vote_state_ret.g_pow_xi_yi_vis[params.cvp_i as usize] = g_pow_xi_yi_vi;
    cast_vote_state_ret.zkp_vis[params.cvp_i as usize] = zkp_vi;

    Ok((A::accept(), cast_vote_state_ret))
}

pub fn check_valid2<Z : Z_Field, G: Group<Z>>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
}

pub fn check_commitment<Z : Z_Field, G: Group<Z>>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
}

pub struct TallyParameter {}
#[hax::receive(contract = "OVN", name = "tally", parameter = "TallyParameter")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "tally", parameter = "TallyParameter"))]
/** Anyone can tally the votes */
pub fn tally_votes<Z : Z_Field, G: Group<Z>, const n : usize, A: HasActions>(
    _: &impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    for i in 0..n {
        check_valid2::<Z, G>(state.g_pow_xi_yi_vis[i], state.zkp_vis[i]);
        check_commitment::<Z, G>(state.g_pow_xi_yi_vis[i], state.commit_vis[i]);
        ()
    }

    let mut vote_result = G::group_one();
    for g_pow_vote in state.g_pow_xi_yi_vis {
        vote_result = G::prod(vote_result, g_pow_vote);
    }

    let mut tally = 0;
    let mut curr = Z::field_zero();
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if G::g_pow(curr) == vote_result {
            tally = i;
        }

        curr = Z::add(curr, Z::field_one());
    }

    let mut tally_votes_state_ret = state.clone();
    tally_votes_state_ret.tally = tally;

    Ok((A::accept(), tally_votes_state_ret))
}

#[cfg(test)]
#[concordium_test]
pub fn test_correctness<Z : Z_Field, G: Group<Z>>() {
    let randomness: Vec<u32> = Vec::new();
    let votes: Vec<bool> = Vec::new();

    // Setup the context
    let mut ctx = InitContextTest::empty();
    // ctx.set_sender(ADDRESS_0);

    let mut state = init_ovn_contract();

    let xis = Vec::new();
    for i in 0..n {
        xis.push(select_private_voting_key::<Z, G>(randomness[i]));
    }

    for i in 0..n {
        let parameter = RegisterParam {
            rp_i: i,
            rp_xi: xis[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        register_vote(ctx, state);
    }

    for i in 0..n {
        let parameter = CastVoteParam::<Z> {
            cvp_i: i,
            cvp_xi: xis[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        commit_to_vote(ctx, state);
    }

    for i in 0..n {
        let parameter = CastVoteParam::<Z> {
            cvp_i: i,
            cvp_xi: xis[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        cast_vote(ctx, state);
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx.set_parameter(&parameter_bytes);

    tally_votes(ctx, state);

    let mut count = 0;
    for v in votes {
        if v {
            count = count + 1; // += 1 does not work correctly
        }
    }

    claim_eq!(
        state.tally,
        count,
        "The tally should equal the number of positive votes"
    );
}
