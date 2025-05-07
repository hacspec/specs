#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

use group::{
    ff::{Field},
    Group,
};


use bls12_381::Gt;
type G = Gt;
type Z = <G as Group>::Scalar;

pub fn hash(_inp: Vec<G>) -> Z {
    Z::one()
}

////////////////////
// Implementation //
////////////////////

#[derive(SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit {
    pub schnorr_zkp_u: G,
    pub schnorr_zkp_c: Z,
    pub schnorr_zkp_z: Z,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) */
// https://www.rfc-editor.org/rfc/rfc8235
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp(
    r: Z, // random
    h: G,
    x: Z,
) -> SchnorrZKPCommit {
    let u = <G as Group>::generator() * r; // g ^ r
    let c = hash(vec![<G as Group>::generator(), h, u]);
    let z = r + (c * x);

    return SchnorrZKPCommit {
        schnorr_zkp_u: u,
        schnorr_zkp_c: c,
        schnorr_zkp_z: z,
    };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp_validate(h: G, pi: SchnorrZKPCommit) -> bool {
    pi.schnorr_zkp_c == hash(vec![<G as Group>::generator(), h, pi.schnorr_zkp_u])
        && (<G as Group>::generator() * pi.schnorr_zkp_z
            == (pi.schnorr_zkp_u + (h * pi.schnorr_zkp_c)))
}

#[derive(SchemaType, Clone, Copy)]
pub struct OrZKPCommit {
    pub or_zkp_x: G,
    pub or_zkp_y: G,
    pub or_zkp_a1: G,
    pub or_zkp_b1: G,
    pub or_zkp_a2: G,
    pub or_zkp_b2: G,

    pub or_zkp_c: Z,

    pub or_zkp_d1: Z,
    pub or_zkp_d2: Z,

    pub or_zkp_r1: Z,
    pub or_zkp_r2: Z,
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn zkp_one_out_of_two(
    w: Z, // random
    rand_r: Z,
    rand_d: Z,
    h: G,
    xi: Z,
    vi: bool,
) -> OrZKPCommit {
    if vi {
        let r1 = rand_r;
        let d1 = rand_d;

        let x = <G as Group>::generator() * (xi);
        let y = (h * xi) + <G as Group>::generator();

        let a1 = <G as Group>::generator() * (r1) + (x * d1);
        let b1 = (h * r1) + (y * d1);

        let a2 = <G as Group>::generator() * (w);
        let b2 = h * w;

        let c = hash(vec![x, y, a1, b1, a2, b2]);

        let d2 = c - d1;
        let r2 = w - xi * d2;

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
        let r2 = rand_r;
        let d2 = rand_d;

        let x = <G as Group>::generator() * (xi);
        let y = h * xi;

        let a1 = <G as Group>::generator() * (w);
        let b1 = h * w;

        let a2 = <G as Group>::generator() * (r2) + (x * d2);
        let b2 = (h * r2) + ((y - <G as Group>::generator()) * d2);

        let c = hash(vec![x, y, a1, b1, a2, b2]);

        let d1 = c - d2;
        let r1 = w - xi * d1;

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
pub fn zkp_one_out_of_two_validate(h: G, zkp: OrZKPCommit) -> bool {
    let c = hash(vec![
        zkp.or_zkp_x,
        zkp.or_zkp_y,
        zkp.or_zkp_a1,
        zkp.or_zkp_b1,
        zkp.or_zkp_a2,
        zkp.or_zkp_b2,
    ]); // TODO: add i

    c == zkp.or_zkp_d1 + zkp.or_zkp_d2
        && zkp.or_zkp_a1
            == <G as Group>::generator() * (zkp.or_zkp_r1) + (zkp.or_zkp_x * zkp.or_zkp_d1)
        && zkp.or_zkp_b1 == (h * zkp.or_zkp_r1) + (zkp.or_zkp_y * zkp.or_zkp_d1)
        && zkp.or_zkp_a2
            == <G as Group>::generator() * (zkp.or_zkp_r2) + (zkp.or_zkp_x * zkp.or_zkp_d2)
        && zkp.or_zkp_b2
            == (h * zkp.or_zkp_r2) + ((zkp.or_zkp_y - <G as Group>::generator()) * zkp.or_zkp_d2)
}

pub fn commit_to(g_pow_xi_yi_vi: G) -> Z {
    hash(vec![g_pow_xi_yi_vi])
}

pub fn check_commitment(g_pow_xi_yi_vi: G, commitment: Z) -> bool {
    hash(vec![g_pow_xi_yi_vi]) == commitment
}

#[hax::contract_state(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), contract_state(contract = "OVN"))]
#[derive(SchemaType, Clone, Copy)]
pub struct OvnContractState<const n: usize> {
    pub g_pow_xis: [G; n],
    pub zkp_xis: [SchnorrZKPCommit; n],

    pub commit_vis: [Z; n],

    pub g_pow_xi_yi_vis: [G; n],
    pub zkp_vis: [OrZKPCommit; n],

    pub tally: u32,
}

#[hax::init(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
pub fn init_ovn_contract<const n: usize>(// _: &impl HasInitContext,
) -> InitResult<OvnContractState<n>> {
    Ok(OvnContractState::<n> {
        g_pow_xis: [<G as Group>::identity(); n],
        zkp_xis: [SchnorrZKPCommit {
            schnorr_zkp_u: <G as Group>::identity(),
            schnorr_zkp_z: Z::ZERO,
            schnorr_zkp_c: Z::ZERO,
        }; n],

        commit_vis: [Z::ZERO; n],

        g_pow_xi_yi_vis: [<G as Group>::identity(); n],
        zkp_vis: [OrZKPCommit {
            or_zkp_x: <G as Group>::identity(),
            or_zkp_y: <G as Group>::identity(),
            or_zkp_a1: <G as Group>::identity(),
            or_zkp_b1: <G as Group>::identity(),
            or_zkp_a2: <G as Group>::identity(),
            or_zkp_b2: <G as Group>::identity(),

            or_zkp_c: Z::ZERO,

            or_zkp_d1: Z::ZERO,
            or_zkp_d2: Z::ZERO,

            or_zkp_r1: Z::ZERO,
            or_zkp_r2: Z::ZERO,
        }; n],

        tally: 0,
    })
}

use core::marker::PhantomData;
#[derive(SchemaType)]
pub struct RegisterParam<S: Serialize + From<Z> + Into<Z>> {
    pub rp_i: u32,
    pub rp_xi: Z,
    pub rp_zkp_random: Z,
    pub phantom: PhantomData<S>,
}

impl<S: Serialize + From<Z> + Into<Z>> Serial for RegisterParam<S> {
    fn serial<W: Write>(&self, w: &mut W) -> Result<(), <W as Write>::Err> {
        self.rp_i.serial(w)?;
        <S as From<Z>>::from(self.rp_xi).serial(w)?;
        <S as From<Z>>::from(self.rp_zkp_random).serial(w)?;
        Ok(())
    }
}

impl<S: Serialize + From<Z> + Into<Z>> Deserial for RegisterParam<S> {
    fn deserial<R: Read>(r: &mut R) -> Result<Self, ParseError> {
        let rp_i: u32 = r.get()?;
        let rp_xi: Z = <S as Into<Z>>::into(r.get()?);
        let rp_zkp_random: Z = <S as Into<Z>>::into(r.get()?);
        Ok(RegisterParam {
            rp_i,
            rp_xi,
            rp_zkp_random,
            phantom: PhantomData,
        })
    }
}

/** Primary function in round 1 */
#[hax::receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "register", parameter = "RegisterParam"))]
pub fn register_vote<
    S: Serialize + From<Z> + Into<Z>,
    const n: usize,
    A: HasActions,
>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<n>,
) -> Result<(A, OvnContractState<n>), ParseError> {
    let params: RegisterParam<S> = ctx.parameter_cursor().get()?;
    let g_pow_xi = <G as Group>::generator() * (params.rp_xi);

    let zkp_xi = schnorr_zkp(params.rp_zkp_random, g_pow_xi, params.rp_xi);

    let mut register_vote_state_ret = state.clone();
    register_vote_state_ret.g_pow_xis[params.rp_i as usize] = g_pow_xi;
    register_vote_state_ret.zkp_xis[params.rp_i as usize] = zkp_xi;

    Ok((A::accept(), register_vote_state_ret))
}

#[derive(SchemaType)]
pub struct CastVoteParam<S: Serialize + From<Z> + Into<Z>> {
    pub cvp_i: u32,
    pub cvp_xi: Z,
    pub cvp_zkp_random_w: Z,
    pub cvp_zkp_random_r: Z,
    pub cvp_zkp_random_d: Z,
    pub cvp_vote: bool,
    pub phantom: PhantomData<S>,
}

impl<S: Serialize + From<Z> + Into<Z>> Serial for CastVoteParam<S> {
    fn serial<W: Write>(&self, w: &mut W) -> Result<(), <W as Write>::Err> {
        self.cvp_i.serial(w)?;
        <S as From<Z>>::from(self.cvp_xi).serial(w)?;
        <S as From<Z>>::from(self.cvp_zkp_random_w).serial(w)?;
        <S as From<Z>>::from(self.cvp_zkp_random_r).serial(w)?;
        <S as From<Z>>::from(self.cvp_zkp_random_d).serial(w)?;
        self.cvp_vote.serial(w)?;
        Ok(())
    }
}

impl<S: Serialize + From<Z> + Into<Z>> Deserial for CastVoteParam<S> {
    fn deserial<R: Read>(r: &mut R) -> Result<Self, ParseError> {
        let cvp_i: u32 = r.get()?;
        let cvp_xi: Z = <S as Into<Z>>::into(r.get()?);
        let cvp_zkp_random_w: Z = <S as Into<Z>>::into(r.get()?);
        let cvp_zkp_random_r: Z = <S as Into<Z>>::into(r.get()?);
        let cvp_zkp_random_d: Z = <S as Into<Z>>::into(r.get()?);
        let cvp_vote: bool = r.get()?;
        Ok(CastVoteParam {
            cvp_i,
            cvp_xi,
            cvp_zkp_random_w,
            cvp_zkp_random_r,
            cvp_zkp_random_d,
            cvp_vote,
            phantom: PhantomData,
        })
    }
}

pub fn compute_g_pow_yi<const n: usize>(i: usize, xis: [G; n]) -> G {
    let mut prod1 = <G as Group>::identity();
    for j in 0..i {
        prod1 = prod1 + xis[j];
    }

    let mut prod2 = <G as Group>::identity();
    for j in (i + 1)..n {
        prod2 = prod2 + xis[j];
    }

    // implicitly: Y_i = g^y_i
    let g_pow_yi = prod1 - prod2;
    g_pow_yi
}

pub fn compute_group_element_for_vote(xi: Z, vote: bool, g_pow_yi: G) -> G {
    (g_pow_yi * xi)
        + <G as Group>::generator()
            * (if vote {
                Z::ONE
            } else {
                Z::ZERO
            })
}

/** Commitment before round 2 */
#[hax::receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam"))]
pub fn commit_to_vote<
    S: Serialize + From<Z> + Into<Z>,
    const n: usize,
    A: HasActions,
>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<n>,
) -> Result<(A, OvnContractState<n>), ParseError> {
    let params: CastVoteParam<S> = ctx.parameter_cursor().get()?;

    for i in 0..n {
        if !schnorr_zkp_validate(state.g_pow_xis[i], state.zkp_xis[i]) {
            return Err(ParseError {});
        }
    }

    let g_pow_yi = compute_g_pow_yi::<n>(params.cvp_i as usize, state.g_pow_xis);
    let g_pow_xi_yi_vi = compute_group_element_for_vote(params.cvp_xi, params.cvp_vote, g_pow_yi);
    let commit_vi = commit_to(g_pow_xi_yi_vi);

    let mut commit_to_vote_state_ret = state.clone();
    commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = commit_vi;
    Ok((A::accept(), commit_to_vote_state_ret))
}

/** Primary function in round 2, also opens commitment */
#[hax::receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
// #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam"))]
pub fn cast_vote<
    S: Serialize + From<Z> + Into<Z>,
    const n: usize,
    A: HasActions,
>(
    ctx: impl HasReceiveContext,
    state: OvnContractState<n>,
) -> Result<(A, OvnContractState<n>), ParseError> {
    let params: CastVoteParam<S> = ctx.parameter_cursor().get()?;

    let g_pow_yi = compute_g_pow_yi::<n>(params.cvp_i as usize, state.g_pow_xis);
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
pub fn tally_votes<const n: usize, A: HasActions>(
    _: impl HasReceiveContext,
    state: OvnContractState<n>,
) -> Result<(A, OvnContractState<n>), ParseError> {
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<n>(i as usize, state.g_pow_xis);
        if !zkp_one_out_of_two_validate(g_pow_yi, state.zkp_vis[i]) {
            return Err(ParseError {});
        }
        if !check_commitment(state.g_pow_xi_yi_vis[i], state.commit_vis[i]) {
            return Err(ParseError {});
        }
    }

    let mut vote_result = <G as Group>::identity();
    for g_pow_vote in state.g_pow_xi_yi_vis {
        vote_result = vote_result + g_pow_vote;
    }

    let mut tally = 0;
    let mut curr = Z::ZERO;
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if <G as Group>::generator() * (curr) == vote_result {
            tally = i;
        }

        curr = curr + Z::ONE;
    }

    let mut tally_votes_state_ret = state.clone();
    tally_votes_state_ret.tally = tally;

    Ok((A::accept(), tally_votes_state_ret))
}

// https://github.com/stonecoldpat/anonymousvoting
