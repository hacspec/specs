#![no_std]

// use core::*;
// use hacspec_lib::*;
// use creusot_contracts::*;

use concordium_std::*; // {HasLogger, HasInitContext, Logger, HasContractState, Reject, Serial, Deserial, Read, ParseResult, Write};
use concordium_std_derive::*;

/** Interface for group implementation */
pub trait Group {
    type group_type: PartialEq + Eq + Clone + Copy + concordium_std::Serialize;

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

struct z_17 {}
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
struct OvnContractState<G: Group, const n: usize> {
    broadcast1_a: [G::group_type; n],
    broadcast1_b: [u32; n],

    broadcast2_a: [G::group_type; n],
    broadcast2_b: [G::group_type; n],
    broadcast2_c: [u32; n],

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
pub fn ZKP<G: Group>(xi: u32) -> u32 {
    0
}

#[derive(Serialize, SchemaType)]
struct RegisterParam {
    i: u32,
    xi: u32,
}

type G = z_17;
const n: usize = 20;

/** Primary function in round 1 */
#[receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
pub fn register_vote_pre<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    let params: RegisterParam = ctx.parameter_cursor().get()?;
    // let xi = select_private_voting_key::<G>(params.random);
    state.broadcast1_a[params.i as usize] = G::g_pow(params.xi);
    state.broadcast1_b[params.i as usize] = ZKP::<G>(params.xi);
    Ok(A::accept())
}

pub fn check_valid(zkp: u32) -> bool {
    true
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn ZKP_one_out_of_two(vi: bool) -> u32 {
    32 // TODO
}

#[derive(Serialize, SchemaType)]
struct CastVoteParam {
    i: u32,
    xi: u32,
    vote: bool,
}
/** Primary function in round 2 */
#[receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
pub fn cast_vote<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    let params: CastVoteParam = ctx.parameter_cursor().get()?;
    for zkp in state.broadcast1_b {
        check_valid(zkp);
        ()
    }

    let mut prod1 = G::one();
    for j in 0..(params.i - 1) as usize {
        prod1 = G::prod(prod1, state.broadcast1_a[j]);
    }
    let prod2 = G::one();
    for j in (params.i + 1) as usize..n {
        prod2 = G::prod(prod2, state.broadcast1_a[j]);
    }
    let Yi = G::div(prod1, prod2);
    // implicityly: Y_i = g^y_i

    state.broadcast2_a[params.i as usize] = G::pow(Yi, params.xi);
    state.broadcast2_b[params.i as usize] = G::g_pow(if params.vote { 1 } else { 0 });
    state.broadcast2_c[params.i as usize] = ZKP_one_out_of_two(params.vote);

    Ok(A::accept())
}

struct TallyParameter {}

#[receive(contract = "OVN", name = "tally", parameter = "TallyParameter")]
/** Anyone can tally the votes */
pub fn tally_votes<A: HasActions>(
    _: &impl HasReceiveContext,
    state: &mut OvnContractState<G, n>,
) -> Result<A, ParseError> {
    let (g_pow_xi_yi, g_pow_vi, zkps) =
        (state.broadcast2_a, state.broadcast2_b, state.broadcast2_c);
    for zkp in zkps {
        check_valid(zkp);
        ()
    }

    let mut vote_result = G::one();
    for i in 0..g_pow_vi.len() {
        vote_result = G::prod(
            vote_result,
            G::prod(g_pow_xi_yi[i].clone(), g_pow_vi[i].clone()),
        );
    }

    let mut tally = 0;
    for i in 1..n as u32 {
        // Should be while, but is bounded by n anyways!
        if G::g_pow(i) == vote_result {
            tally = i;
        }
    }
    state.tally = tally;

    Ok(A::accept())
}

// pub fn correctness<G : Group>(randomness : Vec<u32>, votes : Vec<bool>) -> bool {
//     let mut xi = Vec::new();
//     for i in 0..n {
//         xi.push(register_vote_pre::<G>(i, randomness[i]))
//     }
//     let (gs, zkps) = get_broadcast1();
//     let mut Yi = Vec::new();
//     for i in 0..n {
//         Yi.push(register_vote_post::<G>(i, gs.clone(), zkps.clone()));
//     }
//     for i in 0..n {
//         cast_vote::<G>(xi[i], Yi[i], votes[i])
//     }
//     let mut count = 0;
//     for v in votes {
//         if v {
//             count = count + 1; // += 1 does not work correctly
//         }
//     }
//     tally_votes::<G>() == count
// }

// extern crate quickcheck;
// #[macro_use(quickcheck)]
// extern crate quickcheck_macros;
// use quickcheck::*;

// #[ensures(result == true)]
// pub fn temp () {

// }

// #[quickcheck]
// pub fn check_correctness(randomness : Vec<u32>, votes : Vec<bool>) -> bool {
//     correctness::<z_17>(randomness, votes);
// }
