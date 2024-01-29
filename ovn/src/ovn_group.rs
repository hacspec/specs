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

mod ovn_traits;
pub use ovn_traits::*;

////////////////////
// Implementation //
////////////////////

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit<Z: Z_Field, G: Group<Z>> {
    pub schnorr_zkp_u: G::group_type,
    pub schnorr_zkp_c: Z::field_type,
    pub schnorr_zkp_z: Z::field_type,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) */
// https://www.rfc-editor.org/rfc/rfc8235
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp<Z: Z_Field, G: Group<Z>>(
    random: u32,
    h: G::group_type,
    x: Z::field_type,
) -> SchnorrZKPCommit<Z, G> {
    let r = Z::random_field_elem(random);
    let u = G::g_pow(r);
    let c = G::hash(vec![G::g(), h, u]);
    let z = Z::add(r, Z::mul(c, x));

    return SchnorrZKPCommit { schnorr_zkp_u: u, schnorr_zkp_c: c, schnorr_zkp_z: z };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp_validate<Z: Z_Field, G: Group<Z>>(
    h: G::group_type,
    pi: SchnorrZKPCommit<Z, G>,
) -> bool {
    pi.schnorr_zkp_c == G::hash(vec![G::g(), h, pi.schnorr_zkp_u]) && G::g_pow(pi.schnorr_zkp_z) == G::prod(pi.schnorr_zkp_u, G::pow(h, pi.schnorr_zkp_c))
}

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OrZKPCommit<Z: Z_Field, G: Group<Z>> {
    pub or_zkp_x: G::group_type,
    pub or_zkp_y: G::group_type,
    pub or_zkp_a1: G::group_type,
    pub or_zkp_b1: G::group_type,
    pub or_zkp_a2: G::group_type,
    pub or_zkp_b2: G::group_type,

    pub or_zkp_c: Z::field_type,

    pub or_zkp_d1: Z::field_type,
    pub or_zkp_d2: Z::field_type,

    pub or_zkp_r1: Z::field_type,
    pub or_zkp_r2: Z::field_type,
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn zkp_one_out_of_two<Z: Z_Field, G: Group<Z>>(
    random_w: u32,
    random_r: u32,
    random_d: u32,
    h: G::group_type,
    xi: Z::field_type,
    vi: bool,
) -> OrZKPCommit<Z, G> {
    let w = Z::random_field_elem(random_w);

    if vi {
        let r1 = Z::random_field_elem(random_r);
        let d1 = Z::random_field_elem(random_d);

        let x = G::g_pow(xi);
        let y = G::prod(G::pow(h, xi), G::g());

        let a1 = G::prod(G::g_pow(r1), G::pow(x, d1));
        let b1 = G::prod(G::pow(h, r1), G::pow(y, d1));

        let a2 = G::g_pow(w);
        let b2 = G::pow(h, w);

        let c = G::hash(vec![x, y, a1, b1, a2, b2]);

        let d2 = Z::sub(c, d1);
        let r2 = Z::sub(w, Z::mul(xi, d2));

        OrZKPCommit {
            or_zkp_x: x,
            or_zkp_y: y,
            or_zkp_a1: a1,
            or_zkp_b1: b1,
            or_zkp_a2: a2,
            or_zkp_b2: b2,
            or_zkp_c: c,
            or_zkp_d1: d1,
            or_zkp_d2: d2,
            or_zkp_r1: r1,
            or_zkp_r2: r2,
        }
    } else {
        let r2 = Z::random_field_elem(random_r);
        let d2 = Z::random_field_elem(random_d);

        let x = G::g_pow(xi);
        let y = G::pow(h, xi);

        let a1 = G::g_pow(w);
        let b1 = G::pow(h, w);

        let a2 = G::prod(G::g_pow(r2), G::pow(x, d2));
        let b2 = G::prod(G::pow(h, r2), G::pow(G::div(y, G::g()), d2));

        let c = G::hash(vec![x, y, a1, b1, a2, b2]);

        let d1 = Z::sub(c, d2);
        let r1 = Z::sub(w, Z::mul(xi, d1));

        OrZKPCommit {
            or_zkp_x: x,
            or_zkp_y: y,
            or_zkp_a1: a1,
            or_zkp_b1: b1,
            or_zkp_a2: a2,
            or_zkp_b2: b2,
            or_zkp_c: c,
            or_zkp_d1: d1,
            or_zkp_d2: d2,
            or_zkp_r1: r1,
            or_zkp_r2: r2,
        }
    }
}

// Anonymous voting by two-round public discussion
pub fn zkp_one_out_of_two_validate<Z: Z_Field, G: Group<Z>>(
    h: G::group_type,
    zkp: OrZKPCommit<Z, G>,
) -> bool {
    let c = G::hash(vec![zkp.or_zkp_x, zkp.or_zkp_y, zkp.or_zkp_a1, zkp.or_zkp_b1, zkp.or_zkp_a2, zkp.or_zkp_b2]); // TODO: add i

    (c == Z::add(zkp.or_zkp_d1, zkp.or_zkp_d2)
        && zkp.or_zkp_a1 == G::prod(G::g_pow(zkp.or_zkp_r1), G::pow(zkp.or_zkp_x, zkp.or_zkp_d1))
        && zkp.or_zkp_b1 == G::prod(G::pow(h, zkp.or_zkp_r1), G::pow(zkp.or_zkp_y, zkp.or_zkp_d1))
        && zkp.or_zkp_a2 == G::prod(G::g_pow(zkp.or_zkp_r2), G::pow(zkp.or_zkp_x, zkp.or_zkp_d2))
        && zkp.or_zkp_b2 == G::prod(G::pow(h, zkp.or_zkp_r2), G::pow(G::div(zkp.or_zkp_y, G::g()), zkp.or_zkp_d2)))
}

pub fn commit_to<Z: Z_Field, G: Group<Z>>(g_pow_xi_yi_vi: G::group_type) -> Z::field_type {
    G::hash(vec![g_pow_xi_yi_vi])
}

pub fn check_commitment<Z: Z_Field, G: Group<Z>>(
    g_pow_xi_yi_vi: G::group_type,
    commitment: Z::field_type,
) -> bool {
    G::hash(vec![g_pow_xi_yi_vi]) == commitment
}

#[hax::contract_state(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), contract_state(contract = "OVN"))]
#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OvnContractState<Z: Z_Field, G: Group<Z>, const n: usize> {
    pub g_pow_xis: [G::group_type; n],
    pub zkp_xis: [SchnorrZKPCommit<Z, G>; n],

    pub commit_vis: [Z::field_type; n],

    pub g_pow_xi_yi_vis: [G::group_type; n],
    pub zkp_vis: [OrZKPCommit<Z, G>; n],

    pub tally: u32,
}

#[hax::init(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
pub fn init_ovn_contract<Z: Z_Field, G: Group<Z>, const n: usize>(// _: &impl HasInitContext,
) -> InitResult<OvnContractState<Z, G, n>> {
    Ok(OvnContractState::<Z, G, n> {
        g_pow_xis: [G::group_one(); n],
        zkp_xis: [SchnorrZKPCommit::<Z, G> {
            schnorr_zkp_u: G::group_one(),
            schnorr_zkp_z: Z::field_zero(),
            schnorr_zkp_c: Z::field_zero(),
        }; n],

        commit_vis: [Z::field_zero(); n],

        g_pow_xi_yi_vis: [G::group_one(); n],
        zkp_vis: [OrZKPCommit::<Z, G> {
            or_zkp_x: G::group_one(),
            or_zkp_y: G::group_one(),
            or_zkp_a1: G::group_one(),
            or_zkp_b1: G::group_one(),
            or_zkp_a2: G::group_one(),
            or_zkp_b2: G::group_one(),

            or_zkp_c: Z::field_zero(),

            or_zkp_d1: Z::field_zero(),
            or_zkp_d2: Z::field_zero(),

            or_zkp_r1: Z::field_zero(),
            or_zkp_r2: Z::field_zero(),
        }; n],

        tally: 0,
    })
}

/** Currently randomness needs to be injected */
pub fn select_private_voting_key<Z: Z_Field>(random: u32) -> Z::field_type {
    Z::random_field_elem(random)
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParam<Z: Z_Field> {
    pub rp_i: u32,
    pub rp_xi: Z::field_type,
    pub rp_zkp_random: u32,
}

/** Primary function in round 1 */
#[hax::receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "register", parameter = "RegisterParam"))]
pub fn register_vote<Z: Z_Field, G: Group<Z>, const n: usize, A: HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    let params: RegisterParam<Z> = ctx.parameter_cursor().get()?;
    let g_pow_xi = G::g_pow(params.rp_xi);

    let zkp_xi = schnorr_zkp::<Z, G>(params.rp_zkp_random, g_pow_xi, params.rp_xi);

    let mut register_vote_state_ret = state.clone();
    register_vote_state_ret.g_pow_xis[params.rp_i as usize] = g_pow_xi;
    register_vote_state_ret.zkp_xis[params.rp_i as usize] = zkp_xi;

    Ok((A::accept(), register_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParam<Z: Z_Field> {
    pub cvp_i: u32,
    pub cvp_xi: Z::field_type,
    pub cvp_zkp_random_w: u32,
    pub cvp_zkp_random_r: u32,
    pub cvp_zkp_random_d: u32,
    pub cvp_vote: bool,
}

pub fn compute_g_pow_yi<Z: Z_Field, G: Group<Z>, const n: usize>(
    i: usize,
    xis: [G::group_type; n],
) -> G::group_type {
    let mut prod1 = G::group_one();
    for j in 0..i {
        prod1 = G::prod(prod1, xis[j]);
    }

    let mut prod2 = G::group_one();
    for j in (i + 1)..n {
        prod2 = G::prod(prod2, xis[j]);
    }

    // implicitly: Y_i = g^y_i
    let g_pow_yi = G::div(prod1, prod2);
    g_pow_yi
}

pub fn compute_group_element_for_vote<Z: Z_Field, G: Group<Z>>(
    xi: Z::field_type,
    vote: bool,
    g_pow_yi: G::group_type,
) -> G::group_type {
    G::prod(
        G::pow(g_pow_yi, xi),
        G::g_pow(if vote {
            Z::field_one()
        } else {
            Z::field_zero()
        }),
    )
}

/** Commitment before round 2 */
#[hax::receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam"))]
pub fn commit_to_vote<Z: Z_Field, G: Group<Z>, const n: usize, A: HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    let params: CastVoteParam<Z> = ctx.parameter_cursor().get()?;

    for i in 0..n {
        if !schnorr_zkp_validate(state.g_pow_xis[i], state.zkp_xis[i]) {
            return Err(ParseError {});
        }
    }

    let g_pow_yi = compute_g_pow_yi::<Z, G, n>(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<Z, G>(params.cvp_xi, params.cvp_vote, g_pow_yi);
    let commit_vi = commit_to::<Z, G>(g_pow_xi_yi_vi);

    let mut commit_to_vote_state_ret = state.clone();
    commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = commit_vi;
    Ok((A::accept(), commit_to_vote_state_ret))
}

/** Primary function in round 2, also opens commitment */
#[hax::receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam"))]
pub fn cast_vote<Z: Z_Field, G: Group<Z>, const n: usize, A: HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    let params: CastVoteParam<Z> = ctx.parameter_cursor().get()?;

    let g_pow_yi = compute_g_pow_yi::<Z, G, n>(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<Z, G>(params.cvp_xi, params.cvp_vote, g_pow_yi);

    let zkp_vi = zkp_one_out_of_two::<Z, G>(
        params.cvp_zkp_random_w,
        params.cvp_zkp_random_r,
        params.cvp_zkp_random_d,
        g_pow_yi,
        params.cvp_xi,
        params.cvp_vote,
    );
    let mut cast_vote_state_ret = state.clone();
    cast_vote_state_ret.g_pow_xi_yi_vis[params.cvp_i as usize] = g_pow_xi_yi_vi;
    cast_vote_state_ret.zkp_vis[params.cvp_i as usize] = zkp_vi;

    Ok((A::accept(), cast_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct TallyParameter {}

#[hax::receive(contract = "OVN", name = "tally", parameter = "TallyParameter")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "tally", parameter = "TallyParameter"))]
/** Anyone can tally the votes */
pub fn tally_votes<Z: Z_Field, G: Group<Z>, const n: usize, A: HasActions>(
    _: impl HasReceiveContext,
    state: OvnContractState<Z, G, n>,
) -> Result<(A, OvnContractState<Z, G, n>), ParseError> {
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<Z, G, n>(i as usize, state.g_pow_xis);
        if !zkp_one_out_of_two_validate::<Z, G>(g_pow_yi, state.zkp_vis[i]) {
            return Err(ParseError {});
        }
        if !check_commitment::<Z, G>(state.g_pow_xi_yi_vis[i], state.commit_vis[i]) {
            return Err(ParseError {});
        }
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

// https://github.com/stonecoldpat/anonymousvoting
