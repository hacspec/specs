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

/** Currently randomness needs to be injected */
pub fn select_private_voting_key<G: Group>(random: u32) -> u32 {
    random % G::q // x_i \in_R Z_q;
}

/** TODO: Non-interactive Schnorr proof using Fiat-Shamir heuristics */
pub fn ZKP<G: Group>(g_pow_xi: G::group_type, xi: u32) -> u32 {
    0
}

/** Primary function in round 1 */
pub fn register_vote<A: HasActions>(i: u32, random: u32) -> () {
    let xi = select_private_voting_key::<G>(random);
    let g_pow_xi = G::g_pow(xi);
    let zkp_xi = ZKP::<G>(g_pow_xi, xi);

    broadcast1(g_pow_xi, zkp_xi);
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
pub fn commit_to_vote(i: u32, xi: u32, vote: bool) -> () {
    let (g_pow_xis, zkp_xis) = get_broadcast1();

    for zkp in zkp_xis {
        check_valid(zkp);
        ()
    }

    let g_pow_xi_yi_vi = compute_group_element_for_vote::<G>(i, xi, vote, g_pow_xis);
    let commit_vi = commit_to::<G>(g_pow_xi_yi_vi);

    broadcast_commit(commit_vi);
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn ZKP_one_out_of_two<G: Group>(g_pow_vi: G::group_type, vi: bool) -> u32 {
    32 // TODO
}

/** Primary function in round 2, also opens commitment */
pub fn cast_vote(i: u32, xi: u32, vote: bool) -> () {
    let (g_pow_xis, zkp_xis) = get_broadcast1();

    let g_pow_xi_yi_vi = compute_group_element_for_vote::<G>(i, xi, vote, g_pow_xis);
    let zkp_vi = ZKP_one_out_of_two::<G>(g_pow_xi_yi_vi, vote);

    broadcast_2(g_pow_xi_yi_vi, zkp_vi);
}

pub fn check_valid2<G: Group>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
}

pub fn check_commitment<G: Group>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
}

/** Anyone can tally the votes */
pub fn tally_votes() -> u32 {
    let (g_pow_xi_yi_vis, zkp_vis) = get_broadcast2();
    let commit_vis = get_broadcast_commit();

    for i in 0..n {
        check_valid2(g_pow_xi_yi_vis[i], zkp_vis[i]);
        check_commitment(g_pow_xi_yi_vis[i], commit_vis[i]);
        ()
    }

    let mut vote_result = G::one();
    for g_pow_vote in g_pow_xi_yi_vis {
        vote_result = G::prod(vote_result, g_pow_vote);
    }

    let mut tally = 0;
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if G::g_pow(i) == vote_result {
            tally = i;
        }
    }

    tally
}
