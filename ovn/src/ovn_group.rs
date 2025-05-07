use hax_lib::{implies, lemma};
#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

pub use crate::ovn_traits::*;

////////////////////////
// Useful definitions //
////////////////////////

fn sub<Z: Field>(x: Z, y: Z) -> Z {
    x + (-y)
}

fn div<G: Group>(x: G, y: G) -> G {
    x * G::group_inv(y)
}

// #[hax_lib::lemma]
// #[hax_lib::requires(true)]
// fn addC<Z: Field>(x: Z, y: Z) -> Proof<{ implies(x != Z::field_zero(), || x + y == y + x) }> {}

////////////////////
// Implementation //
////////////////////

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit<G: Group> {
    pub schnorr_zkp_u: G,
    pub schnorr_zkp_c: G::Z,
    pub schnorr_zkp_z: G::Z,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) */
// https://www.rfc-editor.org/rfc/rfc8235
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp<G: Group>(random: G::Z, h: G, x: G::Z) -> SchnorrZKPCommit<G> {
    let r = random;
    let u = G::g_pow(r);
    let c = G::hash(vec![G::g(), h, u]);
    let z = r + c * x;

    return SchnorrZKPCommit {
        schnorr_zkp_u: u,
        schnorr_zkp_c: c,
        schnorr_zkp_z: z,
    };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp_validate<G: Group>(h: G, pi: SchnorrZKPCommit<G>) -> bool {
    pi.schnorr_zkp_c == G::hash(vec![G::g(), h, pi.schnorr_zkp_u])
        && G::g_pow(pi.schnorr_zkp_z) == pi.schnorr_zkp_u * G::pow(h, pi.schnorr_zkp_c)
}

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OrZKPCommit<G: Group> {
    pub or_zkp_x: G,
    pub or_zkp_y: G,
    pub or_zkp_a1: G,
    pub or_zkp_b1: G,
    pub or_zkp_a2: G,
    pub or_zkp_b2: G,

    pub or_zkp_c: G::Z,

    pub or_zkp_d1: G::Z,
    pub or_zkp_d2: G::Z,

    pub or_zkp_r1: G::Z,
    pub or_zkp_r2: G::Z,
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn zkp_one_out_of_two<G: Group>(
    random_w: G::Z,
    random_r: G::Z,
    random_d: G::Z,
    h: G,
    xi: G::Z,
    vi: bool,
) -> OrZKPCommit<G> {
    let w = random_w;

    if vi {
        let r1 = random_r;
        let d1 = random_d;

        let x = G::g_pow(xi);
        let y = G::pow(h, xi) * G::g();

        let a1 = G::g_pow(r1) * G::pow(x, d1);
        let b1 = G::pow(h, r1) * G::pow(y, d1);

        let a2 = G::g_pow(w);
        let b2 = G::pow(h, w);

        let c = G::hash(vec![x, y, a1, b1, a2, b2]);

        let d2 = sub::<G::Z>(c, d1);
        let r2 = sub::<G::Z>(w, xi * d2);

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
        let r2 = random_r;
        let d2 = random_d;

        let x = G::g_pow(xi);
        let y = G::pow(h, xi);

        let a1 = G::g_pow(w);
        let b1 = G::pow(h, w);

        let a2 = G::g_pow(r2) * G::pow(x, d2);
        let b2 = G::pow(h, r2) * G::pow(div::<G>(y, G::g()), d2);

        let c = G::hash(vec![x, y, a1, b1, a2, b2]);

        let d1 = sub::<G::Z>(c, d2);
        let r1 = sub::<G::Z>(w, xi * d1);

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
pub fn zkp_one_out_of_two_validate<G: Group>(h: G, zkp: OrZKPCommit<G>) -> bool {
    let c = G::hash(vec![
        zkp.or_zkp_x,
        zkp.or_zkp_y,
        zkp.or_zkp_a1,
        zkp.or_zkp_b1,
        zkp.or_zkp_a2,
        zkp.or_zkp_b2,
    ]); // TODO: add i

    (c == zkp.or_zkp_d1 + zkp.or_zkp_d2
        && zkp.or_zkp_a1 == G::g_pow(zkp.or_zkp_r1) * G::pow(zkp.or_zkp_x, zkp.or_zkp_d1)
        && zkp.or_zkp_b1 == G::pow(h, zkp.or_zkp_r1) * G::pow(zkp.or_zkp_y, zkp.or_zkp_d1)
        && zkp.or_zkp_a2 == G::g_pow(zkp.or_zkp_r2) * G::pow(zkp.or_zkp_x, zkp.or_zkp_d2)
        && zkp.or_zkp_b2
            == G::pow(h, zkp.or_zkp_r2) * G::pow(div::<G>(zkp.or_zkp_y, G::g()), zkp.or_zkp_d2))
}

pub fn commit_to<G: Group>(g_pow_xi_yi_vi: G) -> G::Z {
    G::hash(vec![g_pow_xi_yi_vi])
}

pub fn check_commitment<G: Group>(g_pow_xi_yi_vi: G, commitment: G::Z) -> bool {
    G::hash(vec![g_pow_xi_yi_vi]) == commitment
}

#[hax::contract_state(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), contract_state(contract = "OVN"))]
#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OvnContractState<G: Group, const n: usize> {
    pub g_pow_xis: [G; n],
    pub zkp_xis: [SchnorrZKPCommit<G>; n],

    pub commit_vis: [G::Z; n],

    pub g_pow_xi_yi_vis: [G; n],
    pub zkp_vis: [OrZKPCommit<G>; n],

    pub tally: u32,

    pub round1: [bool; n],
}

#[hax::init(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
pub fn init_ovn_contract<G: Group, const n: usize>(// _: &impl HasInitContext,
) -> InitResult<OvnContractState<G, n>> {
    Ok(OvnContractState::<G, n> {
        g_pow_xis: [G::group_one(); n],
        zkp_xis: [SchnorrZKPCommit::<G> {
            schnorr_zkp_u: G::group_one(),
            schnorr_zkp_z: G::Z::field_zero(),
            schnorr_zkp_c: G::Z::field_zero(),
        }; n],

        commit_vis: [G::Z::field_zero(); n],

        g_pow_xi_yi_vis: [G::group_one(); n],
        zkp_vis: [OrZKPCommit::<G> {
            or_zkp_x: G::group_one(),
            or_zkp_y: G::group_one(),
            or_zkp_a1: G::group_one(),
            or_zkp_b1: G::group_one(),
            or_zkp_a2: G::group_one(),
            or_zkp_b2: G::group_one(),

            or_zkp_c: G::Z::field_zero(),

            or_zkp_d1: G::Z::field_zero(),
            or_zkp_d2: G::Z::field_zero(),

            or_zkp_r1: G::Z::field_zero(),
            or_zkp_r2: G::Z::field_zero(),
        }; n],

        tally: 0,

        round1: [false; n],
    })
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParam<Z: Field> {
    pub rp_i: u32,
    pub rp_xi: Z,
    pub rp_zkp_random: Z,
}

/** Primary function in round 1 */
#[hax::receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "register", parameter = "RegisterParam"))]
pub fn register_vote<G: Group, const n: usize, A: HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    let params: RegisterParam<G::Z> = ctx.parameter_cursor().get()?;
    let g_pow_xi = G::g_pow(params.rp_xi);

    let zkp_xi = schnorr_zkp::<G>(params.rp_zkp_random, g_pow_xi, params.rp_xi);

    let mut register_vote_state_ret = state.clone();
    register_vote_state_ret.g_pow_xis[params.rp_i as usize] = g_pow_xi;
    register_vote_state_ret.zkp_xis[params.rp_i as usize] = zkp_xi;
    register_vote_state_ret.round1[params.rp_i as usize] = true;

    Ok((A::accept(), register_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParam<Z: Field> {
    pub cvp_i: u32,
    pub cvp_xi: Z,
    pub cvp_zkp_random_w: Z,
    pub cvp_zkp_random_r: Z,
    pub cvp_zkp_random_d: Z,
    pub cvp_vote: bool,
}

// impl<G : Group> core::ops::Mul for G {
//     type Output = Self;
//     fn mul (self, rhs: Self) {
//         Self::prod(self, rhs)
//     }
// }

pub fn compute_g_pow_yi<G: Group, const n: usize>(i: usize, xis: [G; n]) -> G {
    let mut prod1 = xis[0..i].iter().map(|x| x.clone()).product::<G>();
    let mut prod2 = xis[i + 1..n].iter().map(|x| x.clone()).product::<G>();

    // implicitly: Y_i = g^y_i
    let g_pow_yi = div::<G>(prod1, prod2);
    g_pow_yi
}

pub fn compute_group_element_for_vote<G: Group>(xi: G::Z, vote: bool, g_pow_yi: G) -> G {
    G::pow(g_pow_yi, xi)
        * G::g_pow(if vote {
            G::Z::field_one()
        } else {
            G::Z::field_zero()
        })
}

/** Commitment before round 2 */
#[hax::receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam"))]
pub fn commit_to_vote<G: Group, const n: usize, A: HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    let params: CastVoteParam<G::Z> = ctx.parameter_cursor().get()?;

    for i in 0..n {
        if !schnorr_zkp_validate(state.g_pow_xis[i], state.zkp_xis[i]) || !state.round1[i] {
            return Err(ParseError {});
        }
    }

    let g_pow_yi = compute_g_pow_yi::<G, n>(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<G>(params.cvp_xi, params.cvp_vote, g_pow_yi);
    let commit_vi = commit_to::<G>(g_pow_xi_yi_vi);

    let mut commit_to_vote_state_ret = state.clone();
    commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = commit_vi;
    Ok((A::accept(), commit_to_vote_state_ret))
}

/** Primary function in round 2, also opens commitment */
#[hax::receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam"))]
pub fn cast_vote<G: Group, const n: usize, A: HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    let params: CastVoteParam<G::Z> = ctx.parameter_cursor().get()?;

    let g_pow_yi = compute_g_pow_yi::<G, n>(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<G>(params.cvp_xi, params.cvp_vote, g_pow_yi);

    let zkp_vi = zkp_one_out_of_two::<G>(
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
pub fn tally_votes<G: Group, const n: usize, A: HasActions>(
    _: impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<G, n>(i as usize, state.g_pow_xis);
        if !zkp_one_out_of_two_validate::<G>(g_pow_yi, state.zkp_vis[i]) {
            return Err(ParseError {});
        }
        if !check_commitment::<G>(state.g_pow_xi_yi_vis[i], state.commit_vis[i]) {
            return Err(ParseError {});
        }
    }

    let mut vote_result = G::group_one();
    for g_pow_vote in state.g_pow_xi_yi_vis {
        vote_result = vote_result * g_pow_vote;
    }

    // let tally = (0..(n as u32)).rposition(|i| G::g_pow(i) == vote_result).unwrap() as u32;
    let mut tally = 0;
    let mut curr = G::Z::field_zero();
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if G::g_pow(curr) == vote_result {
            tally = i;
        }

        curr = curr + G::Z::field_one();
    }

    let mut tally_votes_state_ret = state.clone();
    tally_votes_state_ret.tally = tally;

    Ok((A::accept(), tally_votes_state_ret))
}

// https://github.com/stonecoldpat/anonymousvoting
