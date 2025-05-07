#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

pub use crate::ovn_traits::*;

use core::marker::PhantomData;

////////////////////////
// Useful definitions //
////////////////////////

struct OVN<G: Group> {
    pd: core::marker::PhantomData<G>,
}

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit<G: Group> {
    pub schnorr_zkp_u: G,
    pub schnorr_zkp_c: G::Z,
    pub schnorr_zkp_z: G::Z,
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

#[derive(Serialize, SchemaType)]
pub struct RegisterParam<Z: Field> {
    pub rp_i: u32,
    pub rp_xi: Z,
    pub rp_zkp_random: Z,
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

#[derive(Serialize, SchemaType)]
pub struct TallyParameter {}

impl<G: Group> OVN<G> {
    pub fn sub(x: G::Z, y: G::Z) -> G::Z {
        (x + /* field addition */ (-/* field opposite */y))
    }

    pub fn div(x: G, y: G) -> G {
        x * G::group_inv(y) // group product
    }

    ////////////////////
    // Implementation //
    ////////////////////

    /** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) */
    // https://www.rfc-editor.org/rfc/rfc8235
    // https://crypto.stanford.edu/cs355/19sp/lec5.pdf
    pub fn schnorr_zkp(random: G::Z, h: G, x: G::Z) -> SchnorrZKPCommit<G> {
        let r = random;
        let u = G::g_pow(r);
        let c = G::hash(vec![G::g(), h, u]);
        let z = (r + /* field addition */ (c * /* field product */ x));

        return SchnorrZKPCommit {
            schnorr_zkp_u: u,
            schnorr_zkp_c: c,
            schnorr_zkp_z: z,
        };
    }

    // https://crypto.stanford.edu/cs355/19sp/lec5.pdf
    pub fn schnorr_zkp_validate(h: G, pi: SchnorrZKPCommit<G>) -> bool {
        pi.schnorr_zkp_c == G::hash(vec![G::g(), h, pi.schnorr_zkp_u])
            && G::g_pow(pi.schnorr_zkp_z)
                == (pi.schnorr_zkp_u * /* group product */ G::pow(h, pi.schnorr_zkp_c))
    }

    /** Cramer, Damgård and Schoenmakers (CDS) technique */
    pub fn zkp_one_out_of_two(
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
            let y = G::pow(h, xi) * /* group product */ G::g();

            let a1 = G::g_pow(r1) * /* group product */ G::pow(x, d1);
            let b1 = G::pow(h, r1) * /* group product */ G::pow(y, d1);

            let a2 = G::g_pow(w);
            let b2 = G::pow(h, w);

            let c = G::hash(vec![x, y, a1, b1, a2, b2]);

            let d2 = Self::sub(c, d1);
            let r2 = Self::sub(w, xi * /* field product */ d2);

            OrZKPCommit::<G> {
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

            let a2 = G::g_pow(r2) * /* group product */ G::pow(x, d2);
            let b2 = G::pow(h, r2) * /* group product */ G::pow(Self::div(y, G::g()), d2);

            let c = G::hash(vec![x, y, a1, b1, a2, b2]);

            let d1 = Self::sub(c, d2);
            let r1 = Self::sub(w, (xi * /* field product */ d1));

            OrZKPCommit::<G> {
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
    pub fn zkp_one_out_of_two_validate(h: G, zkp: OrZKPCommit<G>) -> bool {
        let c = G::hash(vec![
            zkp.or_zkp_x,
            zkp.or_zkp_y,
            zkp.or_zkp_a1,
            zkp.or_zkp_b1,
            zkp.or_zkp_a2,
            zkp.or_zkp_b2,
        ]); // TODO: add i

        (c == (zkp.or_zkp_d1 + /* field addition */ zkp.or_zkp_d2)
            && zkp.or_zkp_a1
                == (G::g_pow(zkp.or_zkp_r1) * /* group product */ G::pow(zkp.or_zkp_x, zkp.or_zkp_d1))
            && zkp.or_zkp_b1
                == (G::pow(h, zkp.or_zkp_r1) * /* group product */
                 G::pow(zkp.or_zkp_y, zkp.or_zkp_d1))
            && zkp.or_zkp_a2
                == (G::g_pow(zkp.or_zkp_r2) * /* group product */ G::pow(zkp.or_zkp_x, zkp.or_zkp_d2))
            && zkp.or_zkp_b2
                == (G::pow(h, zkp.or_zkp_r2) * /* group product */
                 G::pow(Self::div(zkp.or_zkp_y, G::g()), zkp.or_zkp_d2)))
    }

    pub fn commit_to(g_pow_xi_yi_vi: G) -> G::Z {
        G::hash(vec![g_pow_xi_yi_vi])
    }

    pub fn check_commitment(g_pow_xi_yi_vi: G, commitment: G::Z) -> bool {
        G::hash(vec![g_pow_xi_yi_vi]) == commitment
    }

    #[hax::init(contract = "OVN")]
    // #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
    pub fn init_ovn_contract<const n: usize>(// _: &impl HasInitContext,
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

    /** Primary function in round 1 */
    #[hax::receive(contract = "OVN", name = "register", parameter = "RegisterParam")]
    // #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "register", parameter = "RegisterParam"))]
    pub fn register_vote<const n: usize, A: HasActions>(
        ctx: impl HasReceiveContext,
        state: OvnContractState<G, n>,
    ) -> Result<(A, OvnContractState<G, n>), ParseError> {
        let params: RegisterParam<G::Z> = ctx.parameter_cursor().get()?;
        let g_pow_xi = G::g_pow(params.rp_xi);

        let zkp_xi = Self::schnorr_zkp(params.rp_zkp_random, g_pow_xi, params.rp_xi);

        let mut register_vote_state_ret = state.clone();
        register_vote_state_ret.g_pow_xis[params.rp_i as usize] = g_pow_xi;
        register_vote_state_ret.zkp_xis[params.rp_i as usize] = zkp_xi;
        register_vote_state_ret.round1[params.rp_i as usize] = true;

        Ok((A::accept(), register_vote_state_ret))
    }

    // impl<G : Group> core::ops::Mul for G {
    //     type Output = Self;
    //     fn mul (self, rhs: Self) {
    //         Self::prod(self, rhs)
    //     }
    // }

    pub fn compute_g_pow_yi<const n: usize>(i: usize, xis: [G; n]) -> G {
        let mut prod1 = xis[0..i].iter().map(|x| x.clone()).product::<G>();
        let mut prod2 = xis[i + 1..n].iter().map(|x| x.clone()).product::<G>();

        // implicitly: Y_i = g^y_i
        let g_pow_yi = Self::div(prod1, prod2);
        g_pow_yi
    }

    pub fn compute_group_element_for_vote(xi: G::Z, vote: bool, g_pow_yi: G) -> G {
        (G::pow(g_pow_yi, xi) * /* group product */
                G::g_pow(if vote {
                    G::Z::field_one()
                } else {
                    G::Z::field_zero()
                }))
    }

    /** Commitment before round 2 */
    #[hax::receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam")]
    // #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "commit_to_vote", parameter = "CastVoteParam"))]
    pub fn commit_to_vote<const n: usize, A: HasActions>(
        ctx: impl HasReceiveContext,
        state: OvnContractState<G, n>,
    ) -> Result<(A, OvnContractState<G, n>), ParseError> {
        let params: CastVoteParam<G::Z> = ctx.parameter_cursor().get()?;

        for i in 0..n {
            if !Self::schnorr_zkp_validate(state.g_pow_xis[i], state.zkp_xis[i]) || !state.round1[i]
            {
                return Err(ParseError {});
            }
        }

        let g_pow_yi = Self::compute_g_pow_yi::<n>(params.cvp_i as usize, state.g_pow_xis);
        let g_pow_xi_yi_vi =
            Self::compute_group_element_for_vote(params.cvp_xi, params.cvp_vote, g_pow_yi);
        let commit_vi = Self::commit_to(g_pow_xi_yi_vi);

        let mut commit_to_vote_state_ret = state.clone();
        commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = commit_vi;
        Ok((A::accept(), commit_to_vote_state_ret))
    }

    /** Primary function in round 2, also opens commitment */
    #[hax::receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam")]
    // #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "cast_vote", parameter = "CastVoteParam"))]
    pub fn cast_vote<const n: usize, A: HasActions>(
        ctx: impl HasReceiveContext,
        state: OvnContractState<G, n>,
    ) -> Result<(A, OvnContractState<G, n>), ParseError> {
        let params: CastVoteParam<G::Z> = ctx.parameter_cursor().get()?;

        let g_pow_yi = Self::compute_g_pow_yi::<n>(params.cvp_i as usize, state.g_pow_xis);
        let g_pow_xi_yi_vi =
            Self::compute_group_element_for_vote(params.cvp_xi, params.cvp_vote, g_pow_yi);

        let zkp_vi = Self::zkp_one_out_of_two(
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

    #[hax::receive(contract = "OVN", name = "tally", parameter = "TallyParameter")]
    // #[cfg_attr(not(feature = "hax_compilation"), receive(contract = "OVN", name = "tally", parameter = "TallyParameter"))]
    /** Anyone can tally the votes */
    pub fn tally_votes<const n: usize, A: HasActions>(
        _: impl HasReceiveContext,
        state: OvnContractState<G, n>,
    ) -> Result<(A, OvnContractState<G, n>), ParseError> {
        for i in 0..n {
            let g_pow_yi = Self::compute_g_pow_yi::<n>(i as usize, state.g_pow_xis);
            if !Self::zkp_one_out_of_two_validate(g_pow_yi, state.zkp_vis[i]) {
                return Err(ParseError {});
            }
            if !Self::check_commitment(state.g_pow_xi_yi_vis[i], state.commit_vis[i]) {
                return Err(ParseError {});
            }
        }

        let mut vote_result = G::group_one();
        for g_pow_vote in state.g_pow_xi_yi_vis {
            vote_result = (vote_result * /* group product */ g_pow_vote);
        }

        let mut tally = 0;
        let mut curr = G::Z::field_zero();
        for i in 0..n as u32 {
            // Should be while, but is bounded by n anyways!
            if G::g_pow(curr) == vote_result {
                tally = i;
            }

            curr = (curr + /* field addition */ G::Z::field_one());
        }

        let mut tally_votes_state_ret = state.clone();
        tally_votes_state_ret.tally = tally;

        Ok((A::accept(), tally_votes_state_ret))
    }

    // https://github.com/stonecoldpat/anonymousvoting
}
