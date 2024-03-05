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

mod ovn_z_89;
pub use ovn_z_89::*;

type Z :  = z_89;
type G = g_z_89; // g_z_89
const n: usize = 20;

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit {
    pub schnorr_zkp_u: <G as Group<Z>>::group_type,
    pub schnorr_zkp_c: <Z as Z_Field>::field_type,
    pub schnorr_zkp_z: <Z as Z_Field>::field_type,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) */
// https://www.rfc-editor.org/rfc/rfc8235
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp(random: u32, h: <G as Group<Z>>::group_type, x: <Z as Z_Field>::field_type) -> SchnorrZKPCommit {
    let r = <Z as Z_Field>::random_field_elem(random);
    let u = <G as Group<Z>>::g_pow(r);
    let c = <G as Group<Z>>::hash(vec![<G as Group<Z>>::g(), h, u]);
    let z = <Z as Z_Field>::add(r, <Z as Z_Field>::mul(c, x));

    return SchnorrZKPCommit {
        schnorr_zkp_u: u,
        schnorr_zkp_c: c,
        schnorr_zkp_z: z,
    };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp_validate(h: <G as Group<Z>>::group_type, pi: SchnorrZKPCommit) -> bool {
    pi.schnorr_zkp_c == <G as Group<Z>>::hash(vec![<G as Group<Z>>::g(), h, pi.schnorr_zkp_u])
        && <G as Group<Z>>::g_pow(pi.schnorr_zkp_z) == <G as Group<Z>>::prod(pi.schnorr_zkp_u, <G as Group<Z>>::pow(h, pi.schnorr_zkp_c))
}

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OrZKPCommit {
    pub or_zkp_x: <G as Group<Z>>::group_type,
    pub or_zkp_y: <G as Group<Z>>::group_type,
    pub or_zkp_a1: <G as Group<Z>>::group_type,
    pub or_zkp_b1: <G as Group<Z>>::group_type,
    pub or_zkp_a2: <G as Group<Z>>::group_type,
    pub or_zkp_b2: <G as Group<Z>>::group_type,

    pub or_zkp_c: <Z as Z_Field>::field_type,

    pub or_zkp_d1: <Z as Z_Field>::field_type,
    pub or_zkp_d2: <Z as Z_Field>::field_type,

    pub or_zkp_r1: <Z as Z_Field>::field_type,
    pub or_zkp_r2: <Z as Z_Field>::field_type,
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn zkp_one_out_of_two(
    random_w: u32,
    random_r: u32,
    random_d: u32,
    h: <G as Group<Z>>::group_type,
    xi: <Z as Z_Field>::field_type,
    vi: bool,
) -> OrZKPCommit {
    let w = <Z as Z_Field>::random_field_elem(random_w);

    if vi {
        let r1 = <Z as Z_Field>::random_field_elem(random_r);
        let d1 = <Z as Z_Field>::random_field_elem(random_d);

        let x = <G as Group<Z>>::g_pow(xi);
        let y = <G as Group<Z>>::prod(<G as Group<Z>>::pow(h, xi), <G as Group<Z>>::g());

        let a1 = <G as Group<Z>>::prod(<G as Group<Z>>::g_pow(r1), <G as Group<Z>>::pow(x, d1));
        let b1 = <G as Group<Z>>::prod(<G as Group<Z>>::pow(h, r1), <G as Group<Z>>::pow(y, d1));

        let a2 = <G as Group<Z>>::g_pow(w);
        let b2 = <G as Group<Z>>::pow(h, w);

        let c = <G as Group<Z>>::hash(vec![x, y, a1, b1, a2, b2]);

        let d2 = <Z as Z_Field>::sub(c, d1);
        let r2 = <Z as Z_Field>::sub(w, <Z as Z_Field>::mul(xi, d2));

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
        let r2 = <Z as Z_Field>::random_field_elem(random_r);
        let d2 = <Z as Z_Field>::random_field_elem(random_d);

        let x = <G as Group<Z>>::g_pow(xi);
        let y = <G as Group<Z>>::pow(h, xi);

        let a1 = <G as Group<Z>>::g_pow(w);
        let b1 = <G as Group<Z>>::pow(h, w);

        let a2 = <G as Group<Z>>::prod(<G as Group<Z>>::g_pow(r2), <G as Group<Z>>::pow(x, d2));
        let b2 = <G as Group<Z>>::prod(<G as Group<Z>>::pow(h, r2), <G as Group<Z>>::pow(<G as Group<Z>>::div(y, <G as Group<Z>>::g()), d2));

        let c = <G as Group<Z>>::hash(vec![x, y, a1, b1, a2, b2]);

        let d1 = <Z as Z_Field>::sub(c, d2);
        let r1 = <Z as Z_Field>::sub(w, <Z as Z_Field>::mul(xi, d1));

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
pub fn zkp_one_out_of_two_validate(h: <G as Group<Z>>::group_type, zkp: OrZKPCommit) -> bool {
    let c = <G as Group<Z>>::hash(vec![
        zkp.or_zkp_x,
        zkp.or_zkp_y,
        zkp.or_zkp_a1,
        zkp.or_zkp_b1,
        zkp.or_zkp_a2,
        zkp.or_zkp_b2,
    ]); // TODO: add i

    (c == <Z as Z_Field>::add(zkp.or_zkp_d1, zkp.or_zkp_d2)
        && zkp.or_zkp_a1 == <G as Group<Z>>::prod(<G as Group<Z>>::g_pow(zkp.or_zkp_r1), <G as Group<Z>>::pow(zkp.or_zkp_x, zkp.or_zkp_d1))
        && zkp.or_zkp_b1
            == <G as Group<Z>>::prod(
                <G as Group<Z>>::pow(h, zkp.or_zkp_r1),
                <G as Group<Z>>::pow(zkp.or_zkp_y, zkp.or_zkp_d1),
            )
        && zkp.or_zkp_a2 == <G as Group<Z>>::prod(<G as Group<Z>>::g_pow(zkp.or_zkp_r2), <G as Group<Z>>::pow(zkp.or_zkp_x, zkp.or_zkp_d2))
        && zkp.or_zkp_b2
            == <G as Group<Z>>::prod(
                <G as Group<Z>>::pow(h, zkp.or_zkp_r2),
                <G as Group<Z>>::pow(<G as Group<Z>>::div(zkp.or_zkp_y, <G as Group<Z>>::g()), zkp.or_zkp_d2),
            ))
}

pub fn commit_to(g_pow_xi_yi_vi: <G as Group<Z>>::group_type) -> <Z as Z_Field>::field_type {
    <G as Group<Z>>::hash(vec![g_pow_xi_yi_vi])
}

pub fn check_commitment(g_pow_xi_yi_vi: <G as Group<Z>>::group_type, commitment: <Z as Z_Field>::field_type) -> bool {
    <G as Group<Z>>::hash(vec![g_pow_xi_yi_vi]) == commitment
}

#[hax::contract_state(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), contract_state(contract = "OVN"))]
#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OvnContractState {
    pub g_pow_xis: [<G as Group<Z>>::group_type; n],
    pub zkp_xis: [SchnorrZKPCommit; n],

    pub commit_vis: [<Z as Z_Field>::field_type; n],

    pub g_pow_xi_yi_vis: [<G as Group<Z>>::group_type; n],
    pub zkp_vis: [OrZKPCommit; n],

    pub tally: u32,
}

#[hax::init(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
pub fn init_ovn_contract(// _: &impl HasInitContext,
) -> InitResult<OvnContractState> {
    Ok(OvnContractState {
        g_pow_xis: [<G as Group<Z>>::group_one(); n],
        zkp_xis: [SchnorrZKPCommit {
            schnorr_zkp_u: <G as Group<Z>>::group_one(),
            schnorr_zkp_z: <Z as Z_Field>::field_zero(),
            schnorr_zkp_c: <Z as Z_Field>::field_zero(),
        }; n],

        commit_vis: [<Z as Z_Field>::field_zero(); n],

        g_pow_xi_yi_vis: [<G as Group<Z>>::group_one(); n],
        zkp_vis: [OrZKPCommit {
            or_zkp_x: <G as Group<Z>>::group_one(),
            or_zkp_y: <G as Group<Z>>::group_one(),
            or_zkp_a1: <G as Group<Z>>::group_one(),
            or_zkp_b1: <G as Group<Z>>::group_one(),
            or_zkp_a2: <G as Group<Z>>::group_one(),
            or_zkp_b2: <G as Group<Z>>::group_one(),

            or_zkp_c: <Z as Z_Field>::field_zero(),

            or_zkp_d1: <Z as Z_Field>::field_zero(),
            or_zkp_d2: <Z as Z_Field>::field_zero(),

            or_zkp_r1: <Z as Z_Field>::field_zero(),
            or_zkp_r2: <Z as Z_Field>::field_zero(),
        }; n],

        tally: 0,
    })
}

/** Currently randomness needs to be injected */
pub fn select_private_voting_key(random: u32) -> <Z as Z_Field>::field_type {
    <Z as Z_Field>::random_field_elem(random)
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParam {
    pub rp_i: u32,
    pub rp_xi: <Z as Z_Field>::field_type,
    pub rp_zkp_random: u32,
}

/** Primary function in round 1 */
#[hax::receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "register", parameter = "RegisterParam"))]
pub fn register_vote<A : HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState,
) -> Result<(A, OvnContractState), ParseError> {
    let params: RegisterParam = ctx.parameter_cursor().get()?;
    let g_pow_xi = <G as Group<Z>>::g_pow(params.rp_xi);

    let zkp_xi = schnorr_zkp(params.rp_zkp_random, g_pow_xi, params.rp_xi);

    let mut register_vote_state_ret = state.clone();
    register_vote_state_ret.g_pow_xis[params.rp_i as usize] = g_pow_xi;
    register_vote_state_ret.zkp_xis[params.rp_i as usize] = zkp_xi;

    Ok((A::accept(), register_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParam {
    pub cvp_i: u32,
    pub cvp_xi: <Z as Z_Field>::field_type,
    pub cvp_zkp_random_w: u32,
    pub cvp_zkp_random_r: u32,
    pub cvp_zkp_random_d: u32,
    pub cvp_vote: bool,
}

pub fn compute_g_pow_yi(i: usize, xis: [<G as Group<Z>>::group_type; n]) -> <G as Group<Z>>::group_type {
    let mut prod1 = <G as Group<Z>>::group_one();
    for j in 0..i {
        prod1 = <G as Group<Z>>::prod(prod1, xis[j]);
    }

    let mut prod2 = <G as Group<Z>>::group_one();
    for j in (i + 1)..n {
        prod2 = <G as Group<Z>>::prod(prod2, xis[j]);
    }

    // implicitly: Y_i = g^y_i
    let g_pow_yi = <G as Group<Z>>::div(prod1, prod2);
    g_pow_yi
}

pub fn compute_group_element_for_vote(
    xi: <Z as Z_Field>::field_type,
    vote: bool,
    g_pow_yi: <G as Group<Z>>::group_type,
) -> <G as Group<Z>>::group_type {
    <G as Group<Z>>::prod(
        <G as Group<Z>>::pow(g_pow_yi, xi),
        <G as Group<Z>>::g_pow(if vote {
            <Z as Z_Field>::field_one()
        } else {
            <Z as Z_Field>::field_zero()
        }),
    )
}

/** Commitment before round 2 */
#[hax::receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam"))]
pub fn commit_to_vote<A : HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState,
) -> Result<(A, OvnContractState), ParseError> {
    let params: CastVoteParam = ctx.parameter_cursor().get()?;

    for i in 0..n {
        if !schnorr_zkp_validate(state.g_pow_xis[i], state.zkp_xis[i]) {
            return Err(ParseError {});
        }
    }

    let g_pow_yi = compute_g_pow_yi(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi = compute_group_element_for_vote(params.cvp_xi, params.cvp_vote, g_pow_yi);
    let commit_vi = commit_to(g_pow_xi_yi_vi);

    let mut commit_to_vote_state_ret = state.clone();
    commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = commit_vi;
    Ok((A::accept(), commit_to_vote_state_ret))
}

/** Primary function in round 2, also opens commitment */
#[hax::receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam"))]
pub fn cast_vote<A : HasActions>(
    ctx: impl HasReceiveContext,
    state: OvnContractState,
) -> Result<(A, OvnContractState), ParseError> {
    let params: CastVoteParam = ctx.parameter_cursor().get()?;

    let g_pow_yi = compute_g_pow_yi(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi = compute_group_element_for_vote(params.cvp_xi, params.cvp_vote, g_pow_yi);

    let zkp_vi = zkp_one_out_of_two(
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
pub fn tally_votes<A : HasActions>(
    _: impl HasReceiveContext,
    state: OvnContractState,
) -> Result<(A, OvnContractState), ParseError> {
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi(i as usize, state.g_pow_xis);
        if !zkp_one_out_of_two_validate(g_pow_yi, state.zkp_vis[i]) {
            return Err(ParseError {});
        }
        if !check_commitment(state.g_pow_xi_yi_vis[i], state.commit_vis[i]) {
            return Err(ParseError {});
        }
    }

    let mut vote_result = <G as Group<Z>>::group_one();
    for g_pow_vote in state.g_pow_xi_yi_vis {
        vote_result = <G as Group<Z>>::prod(vote_result, g_pow_vote);
    }

    let mut tally = 0;
    let mut curr = <Z as Z_Field>::field_zero();
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if <G as Group<Z>>::g_pow(curr) == vote_result {
            tally = i;
        }

        curr = <Z as Z_Field>::add(curr, <Z as Z_Field>::field_one());
    }

    let mut tally_votes_state_ret = state.clone();
    tally_votes_state_ret.tally = tally;

    Ok((A::accept(), tally_votes_state_ret))
}

// https://github.com/stonecoldpat/anonymousvoting
