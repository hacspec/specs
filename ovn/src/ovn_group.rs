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

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

#[cfg(test)]
use rand::random;

pub trait Z_Field: core::marker::Copy {
    type field_type: PartialEq
        + Eq
        + Clone
        + Copy
        + hacspec_concordium::Serialize
        + core::fmt::Debug;

    fn q() -> Self::field_type;

    fn random_field_elem(random: u32) -> Self::field_type;

    fn field_zero() -> Self::field_type;
    fn field_one() -> Self::field_type;

    fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type;
    fn sub(x: Self::field_type, y: Self::field_type) -> Self::field_type;
    fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type;
}

/** Interface for group implementation */
pub trait Group<Z: Z_Field>: core::marker::Copy {
    type group_type: PartialEq
        + Eq
        + Clone
        + Copy
        + hacspec_concordium::Serialize
        + core::fmt::Debug;

    fn g() -> Self::group_type; // Generator (elemnent of group)

    fn g_pow(x: Z::field_type) -> Self::group_type;
    fn pow(g: Self::group_type, x: Z::field_type) -> Self::group_type; // TODO: Link with q
    fn group_one() -> Self::group_type;
    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type;
    fn inv(x: Self::group_type) -> Self::group_type;
    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type;

    fn hash(x: Vec<Self::group_type>) -> Z::field_type;
}

#[derive(Clone, Copy)]
pub struct z_17 {}
impl Z_Field for z_17 {
    type field_type = u32;
    fn q() -> Self::field_type {
        17u32
    } // Prime order
    fn random_field_elem(random: u32) -> Self::field_type {
        random % (Self::q() - 1)
    }

    fn field_zero() -> Self::field_type {
        0u32
    }

    fn field_one() -> Self::field_type {
        1u32
    }

    fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        (x + y) % (Self::q() - 1)
    }

    fn sub(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        (x + (Self::q() - 1) - y) % (Self::q() - 1)
    }

    fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type {
        (x * y) % (Self::q() - 1)
    }
}

#[derive(Clone, Copy)]
pub struct g_z_17 {}
impl Group<z_17> for g_z_17 {
    type group_type = u32;

    fn g() -> Self::group_type {
        3u32
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self::group_type>) -> <z_17 as Z_Field>::field_type {
        5 // TODO
    }

    fn g_pow(x: <z_17 as Z_Field>::field_type) -> Self::group_type {
        Self::pow(Self::g(), x)
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self::group_type, x: <z_17 as Z_Field>::field_type) -> Self::group_type {
        let mut result = Self::group_one();
        for i in 0..(x % (z_17::q() - 1)) {
            result = Self::prod(result, g);
        }
        result
    }

    fn group_one() -> Self::group_type {
        1
    }

    fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        ((x % z_17::q()) * (y % z_17::q())) % z_17::q()
    }

    fn inv(x: Self::group_type) -> Self::group_type {
        // let mut res = 0;
        // for i in 1..z_17::q() {
        //     if Self::prod(Self::g_pow(i), x) == Self::group_one() {
        //         res = i;
        //     }
        // }
        // res
        [0, 1, 9, 6, 13, 7, 3, 5, 15, 2, 12, 14, 10, 4, 11, 8, 16][x as usize]
    }

    fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type {
        Self::prod(x, Self::inv(y))
    }
}

#[test]
pub fn z_17_correctness() {
    type Z = z_17;
    type G = g_z_17;

    assert!(
        G::g_pow(0) == 1
            && G::g_pow(1) == 3
            && G::g_pow(2) == 9
            && G::g_pow(3) == 10
            && G::g_pow(4) == 13
            && G::g_pow(5) == 5
            && G::g_pow(6) == 15
            && G::g_pow(7) == 11
            && G::g_pow(8) == 16
            && G::g_pow(9) == 14
            && G::g_pow(10) == 8
            && G::g_pow(11) == 7
            && G::g_pow(12) == 4
            && G::g_pow(13) == 12
            && G::g_pow(14) == 2
            && G::g_pow(15) == 6
            && G::g_pow(16) == 1
    )
}

#[test]
pub fn z_17_inv_correctness() {
    type Z = z_17;
    type G = g_z_17;

    // [0, 1, 9, 6, 13, 7, 3, 5, 15, 2, 12, 14, 10, 4, 11, 8, 16]
    assert_eq!(G::inv(0), 0);
    assert_eq!(G::inv(1), 1);
    assert_eq!(G::inv(2), 9);
    assert_eq!(G::inv(3), 6);
    assert_eq!(G::inv(4), 13);
    assert_eq!(G::inv(5), 7);
    assert_eq!(G::inv(6), 3);
    assert_eq!(G::inv(7), 5);
    assert_eq!(G::inv(8), 15);
    assert_eq!(G::inv(9), 2);
    assert_eq!(G::inv(10), 12);
    assert_eq!(G::inv(11), 14);
    assert_eq!(G::inv(12), 10);
    assert_eq!(G::inv(13), 4);
    assert_eq!(G::inv(14), 11);
    assert_eq!(G::inv(15), 8);
    assert_eq!(G::inv(16), 16);
}

// use hacspec_bls12_381::*;
// use hacspec_bls12_381_hash::*;

// #[derive(core::marker::Copy, Clone, PartialEq, Eq)]
// struct Z_curve {
//     val: Scalar,
// }

// impl hacspec_concordium::Deserial for Z_curve {
//     // TODO:
//     fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
//         Err(ParseError {})
//     }
// }

// impl hacspec_concordium::Serial for Z_curve {
//     // TODO:
//     fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
//         Ok(())
//     }
// }

// impl Z_Field for Z_curve {
//     type field_type = Z_curve;

//     fn q() -> Self::field_type {
//         Z_curve {
//             val: Scalar::from_hex("1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"),
//         } // TODO: Scalar::modulo_value;
//     }

//     fn random_field_elem(random: u32) -> Self::field_type {
//         Z_curve {
//             val: Scalar::from_literal(random as u128),
//         }
//     }

//     fn field_zero() -> Self::field_type {
//         Z_curve {
//             val: Scalar::from_literal(0u128),
//         } // Scalar::ZERO()
//     }

//     fn field_one() -> Self::field_type {
//         Z_curve {
//             val: Scalar::from_literal(1u128),
//         } // Scalar::ONE()
//     }

//     fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type {
//         Z_curve { val: x.val + y.val }
//     }

//     fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type {
//         Z_curve { val: x.val * y.val }
//     }
// }

// #[derive(core::marker::Copy, Clone, PartialEq, Eq)]
// struct Group_curve {
//     val: Fp12,
// }

// impl hacspec_concordium::Deserial for Group_curve {
//     // TODO:
//     fn deserial<R: Read>(_source: &mut R) -> ParseResult<Self> {
//         Err(ParseError {})
//     }
// }

// impl hacspec_concordium::Serial for Group_curve {
//     // TODO:
//     fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
//         Ok(())
//     }
// }

// impl Group<Z_curve> for Group_curve {
//     type group_type = Group_curve;

//     // https://eips.ethereum.org/EIPS/eip-2333
//     fn g() -> Self::group_type {
//         Group_curve {
//             val: pairing(g1(), g2()),
//         }
//     } // TODO

//     fn pow(g: Self::group_type, x: <Z_curve as Z_Field>::field_type) -> Self::group_type {
//         Group_curve {
//             val: fp12exp(g.val, x.val),
//         }
//     }

//     fn g_pow(x: <Z_curve as Z_Field>::field_type) -> Self::group_type {
//         Self::pow(Self::g(), x)
//     }

//     fn group_one() -> Self::group_type {
//         Group_curve {
//             val: fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::from_literal(1u128)))),
//         } // ONE
//     }

//     fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type {
//         Group_curve {
//             val: fp12mul(x.val, y.val),
//         }
//     }

//     fn inv(x: Self::group_type) -> Self::group_type {
//         Group_curve {
//             val: fp12inv(x.val),
//         }
//     }

//     fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type {
//         Self::prod(x, Self::inv(y))
//     }

//     fn hash(
//         x: Self::group_type,
//         y: Self::group_type,
//         z: Self::group_type,
//     ) -> <Z_curve as Z_Field>::field_type {
//         // fp_hash_to_field
//         Z_curve::field_one() // TODO: bls12-381 hash to curve?
//     }
// }

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit<Z: Z_Field, G: Group<Z>> {
    u: G::group_type,
    c: Z::field_type,
    z: Z::field_type,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics */
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp<Z: Z_Field, G: Group<Z>>(
    random: u32,
    h: G::group_type,
    x: Z::field_type,
) -> SchnorrZKPCommit<Z, G> {
    let r = Z::random_field_elem(random);
    let u = G::g_pow(r);
    let c = G::hash(vec![G::g(), h, u]);
    let z = Z::add(r, Z::mul(c, x)); // g^(r + c * x) =?= u * (g^x)^c

    return SchnorrZKPCommit { u, c, z };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp_validate<Z: Z_Field, G: Group<Z>>(
    h: G::group_type,
    pi: SchnorrZKPCommit<Z, G>,
) -> bool {
    pi.c == G::hash(vec![G::g(), h, pi.u]) && G::g_pow(pi.z) == G::prod(pi.u, G::pow(h, pi.c))
}

#[test]
pub fn schorr_zkp_correctness() {
    fn test(random_x: u32, random_r: u32) -> bool {
        type Z = z_17;
        type G = g_z_17;

        let x: u32 = Z::random_field_elem(random_x);
        let pow_x = G::g_pow(x);

        let pi: SchnorrZKPCommit<Z, G> = schnorr_zkp(random_r, pow_x, x);

        let valid = schnorr_zkp_validate::<Z, G>(pow_x, pi);
        valid
    }

    QuickCheck::new()
        .tests(10000)
        .quickcheck(test as fn(u32, u32) -> bool)
}

// #[test]
// pub fn schorr_zkp_correctness_bls() {
//     fn test(random_x: u32, random_r: u32) -> bool {
//         type Z = Z_curve;
//         type G = Group_curve;

//         let x = Z::random_field_elem(random_x); // 2 works
//         // let _ = G::g();
//         let pow_x = G::g_pow(x);

//         let pi: SchnorrZKPCommit<Z, G> = schnorr_zkp(random_r, pow_x, x);

//         let valid = schnorr_zkp_validate::<Z, G>(pow_x, pi);
//         valid
//     }

//     QuickCheck::new()
//         .tests(10)
//         .quickcheck(test as fn(u32, u32) -> bool)
// }

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OrZKPCommit<Z: Z_Field, G: Group<Z>> {
    x: G::group_type,
    y: G::group_type,
    a1: G::group_type,
    b1: G::group_type,
    a2: G::group_type,
    b2: G::group_type,

    c: Z::field_type,

    d1: Z::field_type,
    d2: Z::field_type,

    r1: Z::field_type,
    r2: Z::field_type,
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
            x,
            y,
            a1,
            b1,
            a2,
            b2,
            c,
            d1,
            d2,
            r1,
            r2,
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
            x,
            y,
            a1,
            b1,
            a2,
            b2,
            c,
            d1,
            d2,
            r1,
            r2,
        }
    }
}

// Anonymous voting by two-round public discussion
pub fn zkp_one_out_of_two_validate<Z: Z_Field, G: Group<Z>>(
    h: G::group_type,
    zkp: OrZKPCommit<Z, G>,
) -> bool {
    let c = G::hash(vec![zkp.x, zkp.y, zkp.a1, zkp.b1, zkp.a2, zkp.b2]); // TODO: add i

    (c == Z::add(zkp.d1, zkp.d2)
        && zkp.a1 == G::prod(G::g_pow(zkp.r1), G::pow(zkp.x, zkp.d1))
        && zkp.b1 == G::prod(G::pow(h, zkp.r1), G::pow(zkp.y, zkp.d1))
        && zkp.a2 == G::prod(G::g_pow(zkp.r2), G::pow(zkp.x, zkp.d2))
        && zkp.b2 == G::prod(G::pow(h, zkp.r2), G::pow(G::div(zkp.y, G::g()), zkp.d2)))
}

#[test]
pub fn or_zkp_correctness() {
    fn test(
        random_w: u32,
        random_r: u32,
        random_d: u32,
        random_h: u32,
        random_x: u32,
        v: bool,
    ) -> bool {
        type Z = z_17;
        type G = g_z_17;

        let mut h = G::g_pow(Z::random_field_elem(random_h));
        let x = Z::random_field_elem(random_x);
        let pi: OrZKPCommit<Z, G> = zkp_one_out_of_two(random_w, random_r, random_d, h, x, v);
        let valid = zkp_one_out_of_two_validate::<Z, G>(h, pi);
        valid
    }

    QuickCheck::new()
        .tests(10000)
        .quickcheck(test as fn(u32, u32, u32, u32, u32, bool) -> bool)
}

#[hax::contract_state(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), contract_state(contract = "OVN"))]
#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OvnContractState<Z: Z_Field, G: Group<Z>, const n: usize> {
    g_pow_xis: [G::group_type; n],
    zkp_xis: [SchnorrZKPCommit<Z, G>; n],

    commit_vis: [u32; n],

    g_pow_xi_yi_vis: [G::group_type; n],
    zkp_vis: [OrZKPCommit<Z, G>; n],

    tally: u32,
}

#[hax::init(contract = "OVN")]
// #[cfg_attr(not(feature = "hax_compilation"), init(contract = "OVN"))]
pub fn init_ovn_contract<Z: Z_Field, G: Group<Z>, const n: usize>(// _: &impl HasInitContext,
) -> InitResult<OvnContractState<Z, G, n>> {
    Ok(OvnContractState::<Z, G, n> {
        g_pow_xis: [G::group_one(); n],
        zkp_xis: [SchnorrZKPCommit::<Z, G> {
            u: G::group_one(),
            z: Z::field_zero(),
            c: Z::field_zero(),
        }; n],

        commit_vis: [0; n],

        g_pow_xi_yi_vis: [G::group_one(); n],
        zkp_vis: [OrZKPCommit::<Z, G> {
            x: G::group_one(),
            y: G::group_one(),
            a1: G::group_one(),
            b1: G::group_one(),
            a2: G::group_one(),
            b2: G::group_one(),

            c: Z::field_zero(),

            d1: Z::field_zero(),
            d2: Z::field_zero(),

            r1: Z::field_zero(),
            r2: Z::field_zero(),
        }; n],

        tally: 0,
    })
}

/** Currently randomness needs to be injected */
pub fn select_private_voting_key<Z: Z_Field>(random: u32) -> Z::field_type {
    Z::random_field_elem(random) // x_i \in_R Z_q;
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParam<Z: Z_Field> {
    rp_i: u32,
    rp_xi: Z::field_type,
    rp_zkp_random: u32,
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
    cvp_i: u32,
    cvp_xi: Z::field_type,
    cvp_zkp_random_w: u32,
    cvp_zkp_random_r: u32,
    cvp_zkp_random_d: u32,
    cvp_vote: bool,
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

#[test]
pub fn sum_to_zero() {
    type Z = z_17;
    type G = g_z_17;
    const n: usize = 15;
    let mut xis: [<z_17 as Z_Field>::field_type; n] = [0; n];
    let mut g_pow_xis: [<g_z_17 as Group<Z>>::group_type; n] = [0; n];
    use rand::random;
    for i in 0..n {
        xis[i] = Z::random_field_elem(random());
        g_pow_xis[i] = G::g_pow(xis[i]);
    }

    let mut res = G::group_one();
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<Z, G, n>(i, g_pow_xis);
        res = G::prod(res, G::pow(g_pow_yi, xis[i]));
    }
    assert_eq!(res, G::group_one());
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

pub fn commit_to<Z: Z_Field, G: Group<Z>>(x: G::group_type) -> u32 {
    0
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

pub fn check_commitment<Z: Z_Field, G: Group<Z>>(g_pow_xi_yi_vi: G::group_type, zkp: u32) -> bool {
    true
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

// use crate::test_infrastructure::*;

#[cfg(test)]
pub fn test_correctness<Z: Z_Field, G: Group<Z>, const n: usize, A: HasActions>(
    votes: [bool; n],
    xis: [Z::field_type; n],
    rp_zkp_randoms: [u32; n],
    cvp_zkp_random_ws1: [u32; n],
    cvp_zkp_random_rs1: [u32; n],
    cvp_zkp_random_ds1: [u32; n],
    cvp_zkp_random_ws2: [u32; n],
    cvp_zkp_random_rs2: [u32; n],
    cvp_zkp_random_ds2: [u32; n],
) -> bool {
    // Setup the context
    let mut ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();
    // ctx.set_sender(ADDRESS_0);

    let mut state: OvnContractState<Z, G, n> = init_ovn_contract().unwrap();

    for i in 0..n {
        let parameter = RegisterParam::<Z> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i], // TODO
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            register_vote::<Z, G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws1[i],
            cvp_zkp_random_r: cvp_zkp_random_rs1[i],
            cvp_zkp_random_d: cvp_zkp_random_ds1[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            commit_to_vote::<Z, G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state)
                .unwrap();
    }

    for i in 0..n {
        let parameter = CastVoteParam::<Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        (_, state) =
            cast_vote::<Z, G, n, A>(ctx.clone().set_parameter(&parameter_bytes), state).unwrap();
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx = ctx.set_parameter(&parameter_bytes);

    (_, state) = tally_votes::<Z, G, n, A>(ctx.clone(), state).unwrap();

    let mut count = 0u32;
    for v in votes {
        if v {
            count = count + 1; // += 1 does not work correctly
        }
    }

    // claim_eq!(
    //     state.tally,
    //     count,
    //     "The tally should equal the number of positive votes"
    // );

    assert_eq!(state.tally, count);
    state.tally == count
    // true
}

// #[concordium_test]
#[test]
fn test_full_z17() {
    type Z = z_17;
    type G = g_z_17;
    const n: usize = 15;

    use rand::random;
    // rand::SeedableRng::seed_from_u64(32u64); // TODO

    fn test() -> bool {
        let mut votes: [bool; n] = [false; n];
        let mut xis: [<z_17 as Z_Field>::field_type; n] = [0; n];
        let mut rp_zkp_randoms: [u32; n] = [0; n];
        let mut cvp_zkp_random_ws1: [u32; n] = [0; n];
        let mut cvp_zkp_random_rs1: [u32; n] = [0; n];
        let mut cvp_zkp_random_ds1: [u32; n] = [0; n];

        let mut cvp_zkp_random_ws2: [u32; n] = [0; n];
        let mut cvp_zkp_random_rs2: [u32; n] = [0; n];
        let mut cvp_zkp_random_ds2: [u32; n] = [0; n];

        for i in 0..n {
            votes[i] = false; // random();
            xis[i] = Z::random_field_elem(random());
            rp_zkp_randoms[i] = random();
            cvp_zkp_random_ws1[i] = random();
            cvp_zkp_random_rs1[i] = random();
            cvp_zkp_random_ds1[i] = random();
            cvp_zkp_random_ws2[i] = random();
            cvp_zkp_random_rs2[i] = random();
            cvp_zkp_random_ds2[i] = random();
        }
        
        test_correctness::<
                Z,
            G,
            n,
            hacspec_concordium::test_infrastructure::ActionsTree,
            >(
            votes,
            xis,
            rp_zkp_randoms,
            cvp_zkp_random_ws1,
            cvp_zkp_random_rs1,
            cvp_zkp_random_ds1,
            cvp_zkp_random_ws2,
            cvp_zkp_random_rs2,
            cvp_zkp_random_ds2,
        )
    };
    
    QuickCheck::new()
        .tests(10000)
        .quickcheck(test as fn() -> bool)
}

// #[concordium_test]
// fn test_bls12_381() {
//     type Z = Z_curve;
//     type G = Group_curve;
//     const n: usize = 15;

//     use rand::random;
//     // rand::SeedableRng::seed_from_u64(32u64); // TODO

//     test_correctness::<Z, G, n, hacspec_concordium::test_infrastructure::ActionsTree>()
// }