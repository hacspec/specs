use core::*;
use hacspec_lib::*;

pub trait Group {
    type group_type : PartialEq + Eq + Clone + Copy;

    const q : usize; // Prime order
    const g : Self::group_type; // Generator (elemnent of group)

    fn g_pow(x : usize) -> Self::group_type;
    fn one() -> Self::group_type;
    fn prod(x : Self::group_type, y : Self::group_type) -> Self::group_type;
    fn div(x : Self::group_type, y : Self::group_type) -> Self::group_type;
    fn random_element() -> Self::group_type;
}

// struct eligible_votes {
//     v_id : usize,
// }

const n : usize = 3;
// const P : [eligible_votes; 3] = // n = 3
//     [eligible_votes {v_id: 0},
//      eligible_votes {v_id: 1},
//      eligible_votes {v_id: 2}];

pub fn select_private_voting_key<G : Group> (random : usize) -> usize {
    random % G::q // x_i \in_R Z_q;
}

pub fn ZKP<G : Group>(xi : usize) -> usize {
    // TODO: Non-usizeeractive Schnorr proof using Fiat-Shamir heuristics
    0
}

// State of bulletin board
pub fn get_broadcast1() -> (Vec<usize>, Vec<usize>) {
    (Vec::new(), Vec::new())
}

pub fn check_valid(zkp : usize) -> bool {
    true
}

pub fn broadcast1<G : Group>(xi : G::group_type, zkp : usize, i : usize) {
    ()
}

pub fn register_vote<G : Group>(i : usize, random : usize) {
    let xi = select_private_voting_key::<G>(random);
    broadcast1::<G>(G::g_pow(xi), ZKP::<G>(xi), i);
    let (gs, zkps) = get_broadcast1();

    for zkp in zkps {
        check_valid(zkp);
        ()
    }

    let mut prod1 = G::one();
    for j in 0..i-1 {
        prod1 = G::prod(prod1, G::g_pow(gs[j]));
        ()
    }
    let prod2 = G::one();
    for j in i+1..n {
        prod1 = G::prod(prod1, G::g_pow(gs[j]));
        ()
    }
    let Yi = G::div(prod1, prod2);
    // implicityly: Y_i = g^y_i
    ()
}

// Meta Round:

// pub fn round1(user){
//     for x in user {
//         register()
//     }
// }

// Cramer, Damgård and Schoenmakers (CDS) technique
pub fn ZKP_one_out_of_two(vi : bool) -> usize {
    32 // TODO
}

pub fn broadcast2<G : Group> (g_pow_xiyi : G::group_type, g_pow_vi : G::group_type, g_pow_vi_zkp : usize) {
    ()
}

pub fn get_broadcast2<G : Group> () -> (Vec<G::group_type>,Vec<G::group_type>,Vec<usize>) {
    (Vec::new(),Vec::new(),Vec::new())
}

pub fn cast_vote<G : Group>(xi : usize, yi : usize, vi : bool) {
    broadcast2::<G>(G::g_pow(xi * yi), G::g_pow(if vi { 1 } else { 0 }), ZKP_one_out_of_two(vi));
    ()
}

// Meta Round:

// pub fn round2(){
//     for x in user {
//         cast_vote()
//     }
// }

pub fn tally_votes<G : Group>() -> usize {
    let (g_pow_xi_yi, g_pow_vi, zkps) = get_broadcast2::<G>();
    for zkp in zkps {
        check_valid(zkp);
        ()
    }

    let mut vote_result = G::one();
    for i in 0..g_pow_vi.len() {
        vote_result = G::prod(vote_result, G::prod(g_pow_xi_yi[i].clone(), g_pow_vi[i].clone()));
        ()
    }

    let mut tally = 0;
    for i in 1..n { // Should be while, but is bounded by n anyways!
        if G::g_pow(i) == vote_result {
            tally = i;
        }
    }
    tally
}

// Meta Round:

// Tally
