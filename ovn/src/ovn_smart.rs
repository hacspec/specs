#![no_std]

// use core::*;
// use hacspec_lib::*;
// use creusot_contracts::*;

use hacspec_concordium::*; // ::{HasLogger, HasInitContext, Logger, HasContractState, Reject, Serial, Deserial, Read, ParseResult, Write, Get, ParseError, HasReceiveContext, HasActions, Seek, Action, ReceiveContextExtern, ExternContext, Vec, to_bytes, test_infrastructure::InitContextTest};
use hacspec_concordium_derive::*;

/** Interface for group implementation */
pub trait Group {
    type group_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

    const q: u32; // Prime order
    const g: Self::group_type; // Generator (elemnent of group)

    fn g_pow(x: u32) -> Self::group_type;
    fn pow(g: Self::group_type, x: u32) -> Self::group_type;
    fn one() -> Self::group_type;
    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type;
    fn inv(x: Self::group_type) -> Self::group_type;
    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type;
    // fn random_element() -> Self::group_type;
}

pub struct z_17 {}
impl Group for z_17 {
    type group_type = u32;

    const q: u32 = 17; // Prime order
    const g: Self::group_type = 3; // Generator (elemnent of group)

    fn g_pow(x: u32) -> Self::group_type {
        (Self::g ^ x) % Self::q
    }

    fn pow(g: Self::group_type, x: u32) -> Self::group_type {
        (Self::g ^ x) % Self::q
    }

    fn one() -> Self::group_type {
        1
    }

    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        (x * y) % Self::q
    }

    fn inv(x: Self::group_type) -> Self::group_type {
        let mut res = 0;
        for i in 1..Self::q {
            if Self::pow(Self::g, i) == x {
                res = i
            }
        }
        Self::q - res
    }

    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        Self::prod(x, Self::inv(y))
    }
    // fn random_element() -> Self::group_type {

    // }
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

#[contract_state(contract = "OVN")]
#[derive(Serialize, SchemaType)]
pub struct OvnContractState<G: Group, const n: usize> {
    g_pow_xis: [G::group_type; n],
    zkp_xis: [u32; n],

    commit_vis: [u32; n],

    g_pow_xi_yi_vis: [G::group_type; n],
    zkp_vis: [u32; n],

    tally: u32,
}

#[init(contract = "OVN")]
pub fn init_ovn_contract(ctx: &impl HasInitContext) -> Result<bool, ()> {
    Ok(true)
}

/** Currently randomness needs to be injected */
pub fn select_private_voting_key<G: Group>(random: u32) -> u32 {
    random % G::q // x_i \in_R Z_q;
}

/** TODO: Non-interactive Schnorr proof using Fiat-Shamir heuristics */
pub fn ZKP<G: Group>(g_pow_xi: G::group_type, xi: u32) -> u32 {
    0
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParam {
    i: u32,
    xi: u32,
}

type G = z_17;
const n: usize = 20;

/** Primary function in round 1 */
#[receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
pub fn register_vote<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    let params: RegisterParam = ctx.parameter_cursor().get()?;

    // let xi = select_private_voting_key::<G>(params.random);
    let g_pow_xi = G::g_pow(params.xi);
    let zkp_xi = ZKP::<G>(g_pow_xi, params.xi);

    state.g_pow_xis[params.i as usize] = g_pow_xi;
    state.zkp_xis[params.i as usize] = zkp_xi;
    Ok(A::accept())
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParam {
    i: u32,
    xi: u32,
    vote: bool,
}

pub fn check_valid(zkp: u32) -> bool {
    true
}

pub fn compute_group_element_for_vote<G: Group>(
    i: u32,
    xi: u32,
    vote: bool,
    xis: [G::group_type; n],
) -> G::group_type {
    let mut prod1 = G::one();
    for j in 0..(i - 1) as usize {
        prod1 = G::prod(prod1, xis[j]);
    }
    let mut prod2 = G::one();
    for j in (i + 1) as usize..n {
        prod2 = G::prod(prod2, xis[j]);
    }
    let Yi = G::div(prod1, prod2);
    // implicityly: Y_i = g^y_i
    G::prod(G::pow(Yi, xi), G::g_pow(if vote { 1 } else { 0 }))
}

pub fn commit_to<G: Group>(x: G::group_type) -> u32 {
    0
}

/** Commitment before round 2 */
#[receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
pub fn commit_to_vote<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    let params: CastVoteParam = ctx.parameter_cursor().get()?;
    for zkp in state.zkp_xis {
        check_valid(zkp);
        ()
    }

    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<G>(params.i, params.xi, params.vote, state.g_pow_xis);
    let commit_vi = commit_to::<G>(g_pow_xi_yi_vi);

    state.commit_vis[params.i as usize] = commit_vi;
    Ok(A::accept())
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn ZKP_one_out_of_two<G: Group>(g_pow_vi: G::group_type, vi: bool) -> u32 {
    32 // TODO
}

/** Primary function in round 2, also opens commitment */
#[receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
pub fn cast_vote<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    let params: CastVoteParam = ctx.parameter_cursor().get()?;

    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<G>(params.i, params.xi, params.vote, state.g_pow_xis);
    let zkp_vi = ZKP_one_out_of_two::<G>(g_pow_xi_yi_vi, params.vote);

    state.g_pow_xi_yi_vis[params.i as usize] = g_pow_xi_yi_vi;
    state.zkp_vis[params.i as usize] = zkp_vi;

    Ok(A::accept())
}

pub fn check_valid2<G: Group>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
}

pub fn check_commitment<G: Group>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
}

pub struct TallyParameter {}
#[receive(contract = "OVN", name = "tally", parameter = "TallyParameter")]
/** Anyone can tally the votes */
pub fn tally_votes<A: HasActions>(
    _: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    for i in 0..n {
        check_valid2::<G>(state.g_pow_xi_yi_vis[i], state.zkp_vis[i]);
        check_commitment::<G>(state.g_pow_xi_yi_vis[i], state.commit_vis[i]);
        ()
    }

    let mut vote_result = G::one();
    for g_pow_vote in state.g_pow_xi_yi_vis {
        vote_result = G::prod(vote_result, g_pow_vote);
    }

    let mut tally = 0;
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if G::g_pow(i) == vote_result {
            tally = i;
        }
    }
    state.tally = tally;

    Ok(A::accept())
}

// #[cfg(test)]
// #[concordium_test]
// pub fn test_correctness<G : Group>() {
//     let randomness : Vec<u32> = Vec::new();
//     let votes : Vec<bool> = Vec::new();

//     // Setup the context
//     let mut ctx = InitContextTest::empty();
//     // ctx.set_sender(ADDRESS_0);

//     let mut state = init_ovn_contract();

//     let xis = Vec::new();
//     for i in 0..n {
//         xis.push(select_private_voting_key::<G>(randomness[i]));
//     }

//     for i in 0..n {
//         let parameter = RegisterParam { i, xi: xis[i] };
//         let parameter_bytes = to_bytes(&parameter);
//         ctx.set_parameter(&parameter_bytes);

//         register_vote(ctx, state);
//     }

//     for i in 0..n {
//         let parameter = CastVoteParam { i, xi: xis[i], vote: votes[i] };
//         let parameter_bytes = to_bytes(&parameter);
//         ctx.set_parameter(&parameter_bytes);

//         commit_to_vote(ctx, state);
//     }

//     for i in 0..n {
//         let parameter = CastVoteParam { i, xi: xis[i], vote: votes[i] };
//         let parameter_bytes = to_bytes(&parameter);
//         ctx.set_parameter(&parameter_bytes);

//         cast_vote(ctx, state);
//     }

//     let parameter = TallyParameter {};
//     let parameter_bytes = to_bytes(&parameter);
//     ctx.set_parameter(&parameter_bytes);

//     tally_votes(ctx, state);

//     let mut count = 0;
//     for v in votes {
//         if v {
//             count = count + 1; // += 1 does not work correctly
//         }
//     }

//     claim_eq!(state.tally, count, "The tally should equal the number of positive votes");
// }
