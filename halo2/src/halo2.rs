#![doc = include_str!("../table.md")]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_lib::*;
use hacspec_pasta::*;

/// Common Reference Struct
///
/// This struct is a global variable for the proving system and holds values used in the commitment schemes
///
/// # Tuple entries
/// * `0`: Seq<G1_pallas> ∈ Gᵈ (vector of random elems.)
/// * `1`: G1_pallas in G (random group element)
type CRS = (Seq<G1_pallas>, G1_pallas);

/// Rotate a polynomial
///
/// # Arguments
///
/// * `p` - the polynomial to rotate
/// * `rotation` - the rotation used (suitable for primitive roots of unity)
fn rotate_polyx(p: Polyx, rotation: FpVesta) -> Polyx {
    let mut res = p;
    for i in 0..res.len() {
        let coef = res[i];
        let rot = rotation.pow(i as u128);
        res[i] = coef * rot;
    }

    res
}

/// Pedersen vector commitment
///
/// # Arguments
///
/// * `crs` - the common reference string
/// * `a` - the "vector"
/// * `blinding` - blinding factor
fn commit_polyx(crs: &CRS, a: Polyx, blinding: FpVesta) -> G1_pallas {
    let (G, W) = crs;
    let (f1, f2, b) = W;

    let lhs: G1_pallas = msm(a, G.clone());
    let rhs: G1_pallas = g1mul_pallas(blinding, (f1.clone(), f2.clone(), b.clone()));
    let res: G1_pallas = g1add_pallas(lhs, rhs);

    res
}

/// Inner product, between to equal length vectors of field elements
///
/// # Arguments
///
/// * `u` - LHS vector
/// * `v` - RHS vector
fn inner_product(u: Polyx, v: Polyx) -> FpVesta {
    let mut res = FpVesta::ZERO();
    for i in 0..u.len() {
        res = res + u[i] * v[i];
    }

    res
}

/// Multiscalar multiplicatoin, auxiliary function for Pedersen vector commitment
///
/// # Arguments
///
/// * `a` - sequence of scalars (LHS)
/// * `g` - sequence of group (curve) elements (RHS)
fn msm(a: Polyx, g: Seq<G1_pallas>) -> G1_pallas {
    // initial value is zero
    let mut res: G1_pallas = (FpPallas::ZERO(), FpPallas::ZERO(), true);
    for i in 0..a.len() {
        res = g1add_pallas(res, g1mul_pallas(a[i], g[i]));
    }

    res
}

/// Compute vanishing polynomial over n-order multiplicative subgroup H with root of unity omega
///
/// # Arguments
/// * `omega` - root of unity for the H
/// * `n` - the order of the group
fn compute_vanishing_polynomial(omega: FpVesta, n: usize) -> Polyx {
    let mut vanishing_poly: Polyx = Seq::<FpVesta>::create(1);

    vanishing_poly[usize::zero()] = FpVesta::ONE();
    for i in 0..(n) {
        let eval_point = omega.pow(i as u128);
        let poly_mul_x = multi_poly_with_x(vanishing_poly.clone());
        let poly_mul_scalar: Polyx = mul_scalar_polyx(vanishing_poly.clone(), eval_point.neg());
        vanishing_poly = add_polyx(poly_mul_x, poly_mul_scalar);
    }

    vanishing_poly
}

/// Implementation of the σ mapping from the protocol
///
/// # Arguments
/// * `i` - the i in σ(i)
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
/// * `q` - q, from the protocol represented
fn sigma(i: usize, sigma_list: Seq<usize>, q: Seq<Seq<usize>>) -> Seq<usize> {
    let idx = sigma_list[i];
    q[idx].clone()
}

/// Auxilary function for computing L_j or R_j in step 24
///
/// # Arguments
/// * `p_part` - $p'_{hi}$ for L or  $p'_{lo}$ for R
/// * `b_part` - $b_{lo}$ for L or  $b_{hi}$ for R
/// * `g_part` - $g'_{lo}$ for L or  $g'_{hi}$ for R
/// * `z` - the challenge z from step 21
/// * `U` - group element U from pp
/// * `W` - group element W from pp
fn calculate_L_or_R(
    p_part: Polyx,
    b_part: Polyx,
    g_part: Seq<G1_pallas>,
    z: FpVesta,
    U: G1_pallas,
    W: G1_pallas,
    blinding: FpVesta,
) -> G1_pallas {
    // <p'_part, G'_part>
    let p_g_msm: G1_pallas = msm(p_part.clone(), g_part);
    let p_b_ip: FpVesta = inner_product(p_part, b_part);
    let z_ip: FpVesta = z * p_b_ip;
    let z_ip_U: G1_pallas = g1mul_pallas(z_ip, U);

    let multed_W: G1_pallas = g1mul_pallas(blinding, W);

    let mut part_j: G1_pallas = g1add_pallas(p_g_msm, z_ip_U);
    part_j = g1add_pallas(part_j, multed_W);

    part_j
}

/// Step 4
/// Beginning of the vanishing argument
///
/// # Arguments
/// * `g_prime` - polynomial from step 2
/// * `omega` - a n=2ˆk root of unity (global variable)
/// * `n` - n=2ˆk (global variable)
fn step_4(g_prime: Polyx, omega: FpVesta, n: usize) -> Polyx {
    let vanishing = compute_vanishing_polynomial(omega, n);

    let (h, remainder) = divide_polyx(g_prime, vanishing);

    h
}

/// Step 5
/// split polynomial of degree n_g(n-1)-n up into n_(g-2) polynomials of degree at most n-1
///
/// The polynomials(represented by vectors) are stored in a vectore.
/// This way the index in the outer vector can act as the i when reproducing the original poly:
/// h(X) = SUM from i=0 to n_(g-1) [xˆ(ni)h_i(x)]
/// Where n is a parameter of the prooving system, and h_i is the ith part of the original poly.
///
/// # Arguments
/// * `h` - Polynomial to be split
/// * `n` - defines length of new polynomials (global variable for prooving system)
/// * `n_g` - splits into n_g-2 new polynomials
fn step_5(h: Polyx, n: usize, n_g: usize) -> Seq<Polyx> {
    let h = trim_polyx(h);
    let n_g = n_g;
    let n = n;

    let mut index_in_h = 0;
    let mut poly_parts = Seq::<Polyx>::create(n_g - 1);

    for i in 0..n_g - 1 {
        let mut current_poly_part = Seq::<FpVesta>::create(n);
        for j in 0..n {
            if index_in_h < h.len() {
                current_poly_part[j] = h[index_in_h];
                index_in_h = index_in_h + 1;
            }
        }
        poly_parts[i] = current_poly_part;
    }
    poly_parts
}

/// Step 6
/// commit to each h_i polynomial keeping them in the seq to peserve the power (i)
///
/// # Arguments
/// * `poly_parts` - A sequence of polynomials to be commited to
/// * `crs` - Commen Refernce Struct (Global variable for prooving system)
/// * `blindings` - Sequence of random elements used as blinding factors
///
/// # Constraints
/// * `blindings` should be at least as long as the `poly_parts`
fn step_6(poly_parts: Seq<Polyx>, crs: &CRS, blindings: Polyx) -> Seq<G1_pallas> {
    let mut commitment_seq: Seq<G1_pallas> = Seq::<G1_pallas>::create(poly_parts.len());
    for i in 0..poly_parts.len() {
        let commitment: G1_pallas = commit_polyx(crs, poly_parts[i].clone(), blindings[i]);
        commitment_seq[i] = commitment;
    }
    commitment_seq
}

/// Step 7
/// Computes the sum from step 7 in the protocol description
///
/// # Arguments
/// * `commitment_seq` - is a sequence of commitments
/// * `x` - is the challenge each commitment should be multiplied with
/// * `n` - Global parameter for the prooving system
fn step_7(commitment_seq: Seq<G1_pallas>, x: FpVesta, n: usize) -> G1_pallas {
    let mut result: G1_pallas = g1_default_pallas();
    for i in 0..commitment_seq.len() {
        let power: usize = n * i;
        let x_raised = x.pow(power as u128);
        let intemidiate: G1_pallas = g1mul_pallas(x_raised, commitment_seq[i]);
        result = g1add_pallas(result, intemidiate);
    }
    result
}

/// Step 8
/// This functions calculates h'(X) from the h_i parts created in step 5 and the challenge x
///
/// # Arguments
/// * `h_parts` - Sequence of the h_i parts from step 5
/// * `x` - the challenge from step 5
/// * `n` - n from the protocol
fn step_8(h_parts: Seq<Polyx>, x: FpVesta, n: usize, h_blinds: Seq<FpVesta>) -> (Polyx, FpVesta) {
    let mut res: Polyx = Seq::<FpVesta>::create((1));

    let mut h_prime_blind = FpVesta::ZERO();

    for i in 0..h_parts.len() {
        let power: usize = n * i;
        let x_raised: FpVesta = x.pow(power as u128);
        let h_i: Polyx = h_parts[i].clone();
        let aux_prod: Polyx = mul_scalar_polyx(h_i, x_raised);
        res = add_polyx(res, aux_prod);

        h_prime_blind = h_prime_blind + h_blinds[i] * x_raised;
    }

    (res, h_prime_blind)
}

/// Step 9
/// This functions returns r(x) and creates a seq filled with a_i from the second part of step 9
///
/// # Arguments
/// * `r` - the polynomial from step 3
/// * `a_prime_seq` - A sequence of the a' polynomials from step 1
/// * `omega` - The generator for the evaluations points also a global parameter for the protocol
/// * `p` - a list of sets p_i which contains integers from the protocol
/// * `x` - The challenge from step 7
fn step_9(
    r: Polyx,
    a_prime_seq: Seq<Polyx>,
    omega: FpVesta,
    p: Seq<Seq<usize>>,
    x: FpVesta,
) -> (FpVesta, Seq<Polyx>) {
    let n_a: usize = a_prime_seq.len();
    let mut a_seq: Seq<Polyx> = Seq::<Polyx>::create(n_a);
    for i in 0..n_a {
        let p_i: Seq<usize> = p[i].clone();
        let n_e: usize = p_i.len();
        let a_prime_i: Polyx = a_prime_seq[i].clone();
        let mut a_i_seq: Polyx = Seq::<FpVesta>::create(n_e);
        for j in 0..n_e {
            let p_i_j: usize = p_i[j];
            let argument: FpVesta = omega.pow(p_i_j as u128).mul(x);
            let a_i_j: FpVesta = eval_polyx(a_prime_i.clone(), argument);
            a_i_seq[j] = a_i_j;
        }
        a_seq[i] = a_i_seq;
    }
    let r_x = eval_polyx(r, x);
    (r_x, a_seq)
}

/// Step 10
/// This function initializes the s sequence of length n_a and fills it with polynomials of degree n_e-1 made with legrange interpolation
///
/// # Arguments
/// * `omega` - omega from the protocol
/// * `p` - the p list from the protocol
/// * `x` - the challenge from step 7
/// * `a` - the sequence of sequences from step 9
fn step_10(omega: FpVesta, p: Seq<Seq<usize>>, x: FpVesta, a: Seq<Polyx>) -> Seq<Polyx> {
    let n_a = a.len();
    let mut s = Seq::<Polyx>::create(n_a);
    for i in 0..n_a {
        let a_i = a[i].clone();

        let p_i = p[i].clone();
        let n_e = p_i.len();

        let mut points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::create((n_e));
        for j in 0..n_e {
            let p_i_j: usize = p_i[j];
            let x_j = omega.pow(p_i_j as u128) * x;
            let y_j = a_i[j];
            points[j] = (x_j, y_j);
        }
        let s_i: Polyx = lagrange_polyx(points);
        s[i] = s_i;
    }

    s
}

/// Step 11
/// Get the list of Q's (Q_0, ..., Q_{n_q - 1})
///
/// # Arguments
/// * `n_a` - n_a from the protocol
/// * `x1` - challenge 1
/// * `x2`- challange 2
/// * `H_prime` - H', the computed sum from step 7
/// * `R` - R, commitment from step 3
/// * `a` - A, the list of hiding commitments for a_i's
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
fn step_11(
    n_a: usize,
    x1: FpVesta,
    x2: FpVesta,
    H_prime: G1_pallas,
    R: G1_pallas,
    a: Seq<G1_pallas>,
    q: Seq<Seq<usize>>,
    sigma_list: Seq<usize>,
) -> (Seq<G1_pallas>, FpVesta, FpVesta) {
    let n_q: usize = q.len();
    let mut qs: Seq<G1_pallas> = Seq::<G1_pallas>::create(n_q);
    for i in 0..qs.len() {
        qs[i] = g1_default_pallas();
    }

    // bullet 1
    for i in 0..(n_a) {
        let a_i: G1_pallas = a[i];
        // TODO is this what is meant by Q_sigma(i) ?
        let sigma_i = sigma(i, sigma_list.clone(), q.clone());
        for k in 0..sigma_i.len() {
            let j: usize = sigma_i[k];
            let q_sigma_i: G1_pallas = qs[j];
            let product: G1_pallas = g1mul_pallas(x1, q_sigma_i);
            qs[j] = g1add_pallas(product, a_i);
        }
    }

    // bullet 2
    let x1_squared: FpVesta = x1 * x1;
    let q0: G1_pallas = qs[usize::zero()];
    let product1: G1_pallas = g1mul_pallas(x1_squared, q0);
    let product2: G1_pallas = g1mul_pallas(x1, H_prime);
    let sum1: G1_pallas = g1add_pallas(product1, product2);
    let final_sum: G1_pallas = g1add_pallas(sum1, R);
    qs[usize::zero()] = final_sum;

    (qs, x1, x2)
}

/// Step 12
/// Get the list of q's (q_0, ..., q_{n_q - 1}) and q_blinds (accumulated blindness)
///
/// # Arguments
/// * `n_a` - n_a from the protocol
/// * `x1` - challenge 1
/// * `h_prime` - h', the computed polynomial from [step_8]
/// * `r` - the "random" polynomial from [step_3]
/// * `a_prime` - a', the list of univariate polys from [step_1]
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
/// * `a_blind` - the blindness used in step 1 for the A_i commitments
fn step_12(
    n_a: usize,
    x1: FpVesta,
    h_prime: Polyx,
    r: Polyx,
    a_prime: Seq<Polyx>,
    q: Seq<Seq<usize>>,
    sigma_list: Seq<usize>,
    a_blinds: Polyx,
    r_blind: FpVesta,
    h_prime_blind: FpVesta,
) -> (Seq<Polyx>, Polyx) {
    let n_q: usize = q.len();

    let mut qs: Seq<Polyx> = Seq::<Polyx>::create(n_q);

    // used for f later
    let mut q_blinds = Seq::<FpVesta>::create(n_q);

    // initialize all polys to constant 0
    for i in 0..qs.len() {
        qs[i] = Seq::<FpVesta>::create(1);
    }

    // bullet 1
    for i in 0..(n_a) {
        let a_i: Polyx = a_prime[i].clone();
        let a_blind_i: FpVesta = a_blinds[i];
        let sigma_i: Seq<usize> = sigma(i, sigma_list.clone(), q.clone());
        for j in 0..sigma_i.len() {
            let j: usize = sigma_i[j];
            let q_sigma_i: Polyx = qs[j].clone();
            let product: Polyx = mul_scalar_polyx(q_sigma_i.clone(), x1);
            qs[j] = add_polyx(product, a_i.clone());

            q_blinds[j] = x1 * q_blinds[j] + a_blind_i;
        }
    }

    // bullet 2
    let x1_squared: FpVesta = x1 * x1;
    let q0: Polyx = qs[usize::zero()].clone();
    let product1: Polyx = mul_scalar_polyx(q0, x1_squared);
    let product2: Polyx = mul_scalar_polyx(h_prime, x1);
    let sum1: Polyx = add_polyx(product1, product2);
    let final_sum: Polyx = add_polyx(sum1, r);
    qs[usize::zero()] = final_sum;
    q_blinds[usize::zero()] = x1_squared * q_blinds[usize::zero()];

    q_blinds[usize::zero()] = q_blinds[usize::zero()] + r_blind;
    q_blinds[usize::zero()] = q_blinds[usize::zero()] + h_prime_blind * x1;

    (qs, q_blinds)
}

/// Step 13
/// Get the list of r's (r_0, ..., r_{n_q - 1})
///
/// # Arguments
/// * `n` - n from the protocol
/// * `omega` - omega from the protocol
/// * `x` - the challenge from step 7
/// * `x1` - the challenge from step 11
/// * `r` - r from step 9
/// * `s` - s, the computed polynomials from step 10
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
/// * `g_prime_eval_combined_from_a` - g'(x) calculated from **a**
/// * `g_prime` - the polynomial from step 2
fn step_13(
    n: usize,
    omega: FpVesta,
    x: FpVesta,
    x1: FpVesta,
    r: FpVesta,
    s: Seq<Polyx>,
    q: Seq<Seq<usize>>,
    sigma_list: Seq<usize>,
    g_prime_eval_combined_from_a: FpVesta,
    g_prime: Polyx,
) -> (Seq<Polyx>, Seq<Polyx>) {
    let n_a: usize = s.len();
    let n_q: usize = q.len();
    let mut rs: Seq<Polyx> = Seq::<Polyx>::create(n_q);

    // initialize all polys to constant 0
    for i in 0..rs.len() {
        rs[i] = Seq::<FpVesta>::create(1);
    }

    // bullet 1
    for i in 0..(n_a) {
        let s_i: Polyx = s[i].clone();
        let sigma_i: Seq<usize> = sigma(i, sigma_list.clone(), q.clone());
        for j in 0..sigma_i.len() {
            let j = sigma_i[j];
            let r_sigma_i = rs[j].clone();
            let product = mul_scalar_polyx(r_sigma_i.clone(), x1);
            rs[j] = add_polyx(product, s_i.clone());
        }
    }

    // the calculation until now is the same
    let mut rs_verifier = rs.clone();
    let mut rs_prover = rs;

    // bullet 2
    // PPROVER WORKS HERE
    let g_prime_x: FpVesta = eval_polyx(g_prime, x);
    let vanishing_poly: Polyx = compute_vanishing_polynomial(omega, n);
    let vanishing_poly_x: FpVesta = eval_polyx(vanishing_poly, x);
    let h = g_prime_x / vanishing_poly_x;
    let x1_squared: FpVesta = x1 * x1;
    let r0: Polyx = rs_prover[usize::zero()].clone();
    let product1 = mul_scalar_polyx(r0, x1_squared);
    let product2 = h * x1;
    let sum1 = add_scalar_polyx(product1, product2);
    let final_sum = add_scalar_polyx(sum1, r);
    rs_prover[usize::zero()] = final_sum;

    // VERIFIER WORKS HERE
    let vanishing_poly: Polyx = compute_vanishing_polynomial(omega, n);
    let vanishing_poly_x: FpVesta = eval_polyx(vanishing_poly, x);
    let h = g_prime_eval_combined_from_a / vanishing_poly_x;
    let x1_squared: FpVesta = x1 * x1;
    let r0: Polyx = rs_verifier[usize::zero()].clone();
    let product1 = mul_scalar_polyx(r0, x1_squared);
    let product2 = h * x1;
    let sum1 = add_scalar_polyx(product1, product2);
    let final_sum = add_scalar_polyx(sum1, r);
    rs_verifier[usize::zero()] = final_sum;

    (rs_prover, rs_verifier)
}

/// Step 14
/// Get the commitment Q', poly q' and the blindness used
///
/// # Arguments
/// * `crs` - the common reference string
/// * `x2` - the challenge from step 11
/// * `q_polys` - the q polynomials from step 12
/// * `r_polys` - the r polynomials from step 13
/// * `q` - q, from the protocol
/// * `blinding` - randomness for commiting
/// * `x` - the challenge from step 7
fn step_14(
    crs: &CRS,
    x2: FpVesta,
    q_polys: Seq<Polyx>,
    r_polys: Seq<Polyx>,
    q: Seq<Seq<usize>>,
    blinding: FpVesta,
    omega: FpVesta,
    x: FpVesta,
) -> (G1_pallas, Polyx, FpVesta) {
    let mut q_prime: Polyx = Seq::<FpVesta>::create(1); // initialize q' to the constant zero poly
    let n_q: usize = q.len();
    for i in 0..(n_q) {
        let x2_powered: FpVesta = x2.pow((n_q - 1 - i) as u128);
        let q_poly_i: Polyx = q_polys[i].clone();
        let r_i: Polyx = r_polys[i].clone();
        let q_i_sub_r_i: Polyx = sub_polyx(q_poly_i, r_i);
        let q_i: Seq<usize> = q[i].clone();
        let mut divisor: Polyx = Seq::<FpVesta>::create(1);
        divisor[usize::zero()] = FpVesta::ONE();

        for j in 0..(q_i.len()) {
            let q_i_j: usize = q_i[j];
            let scalar: FpVesta = omega.pow(q_i_j as u128).mul(x);
            let divisor_mul_x: Polyx = multi_poly_with_x(divisor.clone());
            let divisor_mul_scalar: Polyx = mul_scalar_polyx(divisor.clone(), scalar.neg());
            divisor = add_polyx(divisor_mul_x, divisor_mul_scalar);
        }

        let (divided_poly, remainder) = divide_polyx(q_i_sub_r_i.clone(), divisor);

        let multed_poly: Polyx = mul_scalar_polyx(divided_poly, x2_powered);

        q_prime = add_polyx(q_prime, multed_poly);
    }
    let commitment: G1_pallas = commit_polyx(crs, q_prime.clone(), blinding);

    (commitment, q_prime, blinding)
}

/// Step 15
/// This function emulates sending a challenge.
///
/// # Arguments
///  * `x_3` - the challenge to be send
fn step_15(x_3: FpVesta) -> FpVesta {
    x_3
}

/// Step 16
/// Get the u ∈ F^{n_q} vector
///
/// # Arguments
/// * `n_q` - n_q from the protocol
/// * `x3` - the challenge from step 15
/// * `q_polys` - the q polynomials from step 12
fn step_16(n_q: usize, x3: FpVesta, q_polys: Seq<Polyx>) -> Polyx {
    let mut u: Polyx = Seq::<FpVesta>::create(n_q);
    for i in 0..(n_q) {
        let q_i: Polyx = q_polys[i].clone();
        let u_i: FpVesta = eval_polyx(q_i, x3);
        u[i] = u_i;
    }

    u
}

/// Step 17
/// This function emulates sending a challenge.
///
/// # Arguments
///  * `x_4` - the challenge to be send
fn step_17(x_4: FpVesta) -> FpVesta {
    x_4
}

/// Step 18
/// Get P and the v
///
/// # Arguments
/// * `x` - challenge from step 7
/// * `x1` - challenge from step 11
/// * `x2` - challenge from step 11
/// * `x3` - challenge from step 15
/// * `x4` - challenge from step 17
/// * `omega` - omega from the protocol
/// * `Q_prime` - commitment from step 14
/// * `Q` - list of group-elements from step 11
/// * `u` - list of scalars from step 16
/// * `r` - list of polynomials from step 13
/// * `q` - q, from the protocol
fn step_18(
    x: FpVesta,
    x1: FpVesta,
    x2: FpVesta,
    x3: FpVesta,
    x4: FpVesta,
    omega: FpVesta,
    Q_prime: G1_pallas,
    Q: Seq<G1_pallas>,
    u: Polyx,
    r: Seq<Polyx>,
    q: Seq<Seq<usize>>,
) -> (G1_pallas, FpVesta) {
    let n_q = q.len();
    let v = FpVesta::ZERO();

    let mut P_sum: G1_pallas = g1_default_pallas();
    for i in 0..n_q {
        let Q_i: G1_pallas = Q[i];
        let term: G1_pallas = g1mul_pallas(x4.pow((n_q - i - 1) as u128), Q_i);
        P_sum = g1add_pallas(P_sum, term)
    }
    let first_term: G1_pallas = g1mul_pallas(x4.pow(n_q as u128), Q_prime);
    let P: G1_pallas = g1add_pallas(first_term, P_sum);

    let mut v_first_sum: FpVesta = FpVesta::ZERO();
    for i in 0..n_q {
        let q_i: Seq<usize> = q[i].clone();
        let n_e: usize = q_i.len();
        let u_i: FpVesta = u[i];
        let r_i: Polyx = r[i].clone();
        let r_i_x3: FpVesta = eval_polyx(r_i, x3);
        let numerator: FpVesta = u_i - r_i_x3;
        let mut product: FpVesta = FpVesta::ONE();
        for j in 0..n_e {
            let q_i_j: usize = q_i[j];
            let rhs = omega.pow(q_i_j as u128) * x;
            let term = x3 - rhs;
            product = product * term;
        }
        let sum_term: FpVesta = x2.pow((n_q - i - 1) as u128) * (numerator / product);

        v_first_sum = v_first_sum + sum_term;
    }
    v_first_sum = v_first_sum * x4.pow(n_q as u128);

    let mut v_second_sum: FpVesta = FpVesta::ZERO();
    for i in 0..n_q {
        let u_i: FpVesta = u[i];
        let term: FpVesta = x4.pow((n_q - 1 - i) as u128) * u_i;
        v_second_sum = v_second_sum + term;
    }
    let v = v_first_sum + v_second_sum;
    (P, v)
}

/// Step 19
/// Get the p(X) polynomial
///
/// # Arguments
/// * `x4` - the challenge from step 17
/// * `q_prime` - the q' polynomial computed by the prover in step 14
/// * `q_polys` - the q polynomials from step 12
/// * `q_blinds` - the blinds from step 12
/// * `q_prime_blind` - the blinding from step 14
fn step_19(
    x4: FpVesta,
    q_prime: Polyx,
    q_polys: Seq<Polyx>,
    q_blinds: Polyx,
    q_prime_blind: FpVesta,
) -> (Polyx, FpVesta) {
    let mut p = Seq::<FpVesta>::create(1); // initialize p to the constant zero poly
    let n_q: usize = q_polys.len();

    // used for f later on (accumlated blindness)
    let mut p_blind = FpVesta::ZERO();

    //  Sum_i^nq-1 {x4^(n_q-1-i) q_i(X)}
    for i in 0..n_q {
        let power: usize = (n_q - 1 - i);
        let x4_powered = x4.pow(power as u128);
        let q_i = q_polys[i].clone();
        let multed_poly = mul_scalar_polyx(q_i, x4_powered);

        p = add_polyx(p, multed_poly);

        p_blind = p_blind + (x4_powered * q_blinds[i]);
    }

    // q'(X) + [x4] Sum_i^nq-1 {x4^i q_i(X)}
    let x4n_q: FpVesta = x4.pow(n_q as u128);
    let first_term: Polyx = mul_scalar_polyx(q_prime, x4n_q);
    p = add_polyx(p, first_term);

    p_blind = p_blind + (x4n_q * q_prime_blind);

    (p, p_blind)
}

/// Step 20
/// Get the commitment S and the blindness used
///
/// # Arguments
/// * `s` - a randomly sampled poly (degree n-1) with a root at x3 from [step_15]
/// * `crs` - the common reference string
/// * `r` - randomness for commiting
fn step_20(s: Polyx, crs: CRS, r: FpVesta) -> (G1_pallas, FpVesta) {
    let S: G1_pallas = commit_polyx(&crs, s, r);
    (S, r)
}

/// Step 21
/// Get the xi and z challenges. They have to be fed into hacspec, since there is no randomness.
///
/// # Arguments
/// * `xi` - the ξ challenge
/// * `z` - the z challenge
fn step_21(xi: FpVesta, z: FpVesta) -> (FpVesta, FpVesta) {
    (xi, z)
}

/// Step 22
/// Get the P' curve-point/group-element
///
/// # Arguments
/// * `p` - the group element from step 18
/// * `g0` - the group element at index zero in **G** from pp
/// * `s` - the group element/commitment from step 20
/// * `v` - v as calculated in step 18
/// * `xi` - the ξ challenge from step 21
fn step_22(p: G1_pallas, g0: G1_pallas, s: G1_pallas, v: FpVesta, xi: FpVesta) -> G1_pallas {
    let prod1: G1_pallas = g1mul_pallas(v, g0);
    let prod1_neg: G1_pallas = g1neg_pallas(prod1);
    let prod2: G1_pallas = g1mul_pallas(xi, s);
    let lhs_sum: G1_pallas = g1add_pallas(p, prod1_neg);
    let p_prime: G1_pallas = g1add_pallas(lhs_sum, prod2);
    p_prime
}

/// Step 23
/// Get the p'(X) polynomial and p' blindness
///
/// # Arguments
/// * `p` - the polynomial p from step 19
/// * `s` - the polynomial s from step 20
/// * `x3` - the challenge from step 15
/// * `xi` - the ξ challenge from step 21
/// * `p_blind` - the blindness from step 19
/// * `s_blind` - the blindness from step 20
fn step_23(
    p: Polyx,
    s: Polyx,
    x3: FpVesta,
    xi: FpVesta,
    p_blind: FpVesta,
    s_blind: FpVesta,
) -> (Polyx, FpVesta) {
    let p_eval_x3 = eval_polyx(p.clone(), x3);
    let xi_mul_s = mul_scalar_polyx(s, xi);
    let mut p_prime = p;
    p_prime = sub_scalar_polyx(p_prime, p_eval_x3);
    p_prime = add_polyx(p_prime, xi_mul_s);

    let p_prime_blind = s_blind * xi + p_blind;

    (p_prime, p_prime_blind)
}

/// Step 24
/// Get **G**', **p**', **b**, L, R, and {L,R} blinds
///
/// # Arguments
/// * `p_prime_poly` - the polynomial p'(X) from [step_23]
/// * `G` - the vector of group elems from public-params
/// * `x3` - the challenge from [step_15]
/// * `z` - the challenge from [step_21]
/// * `U` - the group elem U from public-params
/// * `W` - the group elem U from public-params
/// * `n` - n from the protocol preamble
/// * `k` - k from the protocol preamble
/// * `u` - the list of u_j challenges from the verifier
/// * `L_blinding` - the list of blinding to be used for L_j
/// * `R_blinding` - the list of blinding to be used for R_j
///
/// # Returns
/// * `p_prime` - `Seq<Fp>`
/// * `G_prime` - `Seq<G1>`
/// * `b` - `Seq<Fp>`
/// * `L` - `Seq<G1>` the sequence of all `L_j`
/// * `R` - `Seq<G1>` the sequence of all `R_j`
/// * `L_blinding`- `Seq<Fp>` the sequence of blinding used for `L_j`
/// * `R_blinding`- `Seq<Fp>` the sequence of blinding used for `R_j`
fn step_24(
    p_prime_poly: Polyx,
    G: Seq<G1_pallas>,
    x3: FpVesta,
    z: FpVesta,
    U: G1_pallas,
    W: G1_pallas,
    n: usize,
    k: usize,
    u: Polyx,
    L_blinding: Polyx,
    R_blinding: Polyx,
) -> (
    Polyx,
    Seq<G1_pallas>,
    Polyx,
    Seq<G1_pallas>,
    Seq<G1_pallas>,
    Polyx,
    Polyx,
) {
    let mut p_prime: Polyx = p_prime_poly;
    let mut g_prime: Seq<G1_pallas> = G;
    let mut b: Polyx = Seq::<FpVesta>::create(n);
    let mut L: Seq<G1_pallas> = Seq::<G1_pallas>::create(k);
    let mut R: Seq<G1_pallas> = Seq::<G1_pallas>::create(k);

    for i in 0..b.len() {
        let x3_powered: FpVesta = x3.pow(i as u128);
        b[i] = x3_powered;
    }

    for j in 0..k {
        let p_prime_half: usize = p_prime.len() / 2;
        let g_prime_half: usize = g_prime.len() / 2;
        let b_half: usize = b.len() / 2;

        // BULLET 1
        // PROVER WORKS HERE
        let p_prime_lo: Polyx = p_prime.slice(0, p_prime_half);
        let p_prime_hi: Polyx = p_prime.slice(p_prime_half, p_prime_half);

        let g_prime_lo: Seq<G1_pallas> = g_prime.slice(0, g_prime_half);
        let g_prime_hi: Seq<G1_pallas> = g_prime.slice(g_prime_half, g_prime_half);

        let b_lo: Polyx = b.slice(0, b_half);
        let b_hi: Polyx = b.slice(b_half, b_half);

        // calcuate L_j and R_j, using the right parts of p', G' and b
        let L_j: G1_pallas = calculate_L_or_R(
            p_prime_hi.clone(),
            b_lo.clone(),
            g_prime_lo.clone(),
            z,
            U,
            W,
            L_blinding[j],
        );
        L[j] = L_j;

        let R_j: G1_pallas = calculate_L_or_R(
            p_prime_lo.clone(),
            b_hi.clone(),
            g_prime_hi.clone(),
            z,
            U,
            W,
            R_blinding[j],
        );
        R[j] = R_j;

        // BULLET 2
        // VERIFIER WORKS HERE
        let u_j: FpVesta = u[j];

        // BULLET 3
        // VERIFIER & PROVER WORKS HERE
        let mut new_g_prime: Seq<G1_pallas> = Seq::<G1_pallas>::create(g_prime_half);
        for i in 0..new_g_prime.len() {
            // TODO, this is entry-wise multiplication and pairwise addition!!!
            let g_prime_hi_indexed: G1_pallas = g_prime_hi[i];
            let g_prime_lo_indexed: G1_pallas = g_prime_lo[i];
            let rhs_product: G1_pallas = g1mul_pallas(u_j, g_prime_hi_indexed);
            let sum: G1_pallas = g1add_pallas(g_prime_lo_indexed, rhs_product);
            new_g_prime[i] = sum;
        }
        g_prime = new_g_prime;

        let rhs: Polyx = mul_scalar_polyx(b_hi.clone(), u_j);
        let new_b: Polyx = add_polyx(b_lo.clone(), rhs);
        b = new_b;
        // BULLET 4
        // PROVER WORKS HERE
        let u_j_inv: FpVesta = u_j.inv();
        let rhs: Polyx = mul_scalar_polyx(p_prime_hi.clone(), u_j_inv);
        let new_p_prime: Polyx = add_polyx(p_prime_lo.clone(), rhs);
        p_prime = new_p_prime;
    }

    (p_prime, g_prime, b, L, R, L_blinding, R_blinding)
}

/// Step 25
/// Get the zeroth entry in **p** and synthetic blinding factor f
///
/// # Arguments
/// * `p_prime` - **p**' from [step_24]
/// * `L_blinding` - the blinding used for L in step 24
/// * `R_blinding` - the blinding used for R in step 24
/// * `p_prime_blind` - the the accumulated blinding from step 23
/// * `u` - u challenges from 24
fn step_25(
    p_prime: Polyx,
    L_blinding: Polyx,
    R_blinding: Polyx,
    p_prime_blind: FpVesta,
    u: Polyx,
) -> (FpVesta, FpVesta) {
    let c = p_prime[usize::zero()];
    let mut f: FpVesta = p_prime_blind;
    for j in 0..L_blinding.len() {
        let u_j: FpVesta = u[j];
        let u_j_inv: FpVesta = u_j.inv();
        let L_j_blinding: FpVesta = L_blinding[j];
        let R_j_blinding: FpVesta = R_blinding[j];
        f = f + L_j_blinding * u_j_inv;
        f = f + R_j_blinding * u_j;
    }

    (c, f)
}

/// Step 26
/// Verifiers final check of the protocol
///
/// # Arguments
/// * `u` - Sequence of `u_j` from step 24
/// * `L` - Sequence of `L_j` from step 24
/// * `P_prime` -  from step 22
/// * `R` - Sequence of `R_j` from step 24
/// * `c` - from step 25
/// * `G_prime_0` - the first entry in the `G_prime` sequence from step 24
/// * `b_0` - the first entry in the `b` sequence from step 24
/// * `z` - the challenge from step 21
/// * `U` - from public parameters
/// * `f` - blinding factor from step 25
/// * `W` - from public parameters
fn step_26(
    u: Polyx,
    L: Seq<G1_pallas>,
    P_prime: G1_pallas,
    R: Seq<G1_pallas>,
    c: FpVesta,
    G_prime_0: G1_pallas,
    b_0: FpVesta,
    z: FpVesta,
    U: G1_pallas,
    f: FpVesta,
    W: G1_pallas,
) -> bool {
    let mut first_sum: G1_pallas = g1_default_pallas();
    for j in 0..u.len() {
        let u_j_inv: FpVesta = u[j].inv();
        let L_j: G1_pallas = L[j];
        let prod_j: G1_pallas = g1mul_pallas(u_j_inv, L_j);
        first_sum = g1add_pallas(first_sum, prod_j);
    }

    let mut second_sum: G1_pallas = g1_default_pallas();
    for j in 0..u.len() {
        let u_j: FpVesta = u[j];
        let R_j: G1_pallas = R[j];
        let prod_j: G1_pallas = g1mul_pallas(u_j, R_j);
        second_sum = g1add_pallas(second_sum, prod_j);
    }
    let lhs: G1_pallas = g1add_pallas(first_sum, g1add_pallas(P_prime, second_sum));

    let rhs_term_1: G1_pallas = g1mul_pallas(c, G_prime_0);

    let cb_0z: FpVesta = c * b_0 * z;

    let rhs_term_2: G1_pallas = g1mul_pallas(cb_0z, U);

    let rhs_term_3: G1_pallas = g1mul_pallas(f, W);

    let rhs: G1_pallas = g1add_pallas(rhs_term_1, g1add_pallas(rhs_term_2, rhs_term_3));

    let check: bool = lhs == rhs;
    check
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;

#[cfg(test)]
use rand::seq::SliceRandom;
#[cfg(test)]
use rand::thread_rng;

#[cfg(test)]
#[derive(Clone, Debug)]
struct SeqOfUniPoly(Seq<Polyx>);

#[cfg(test)]
#[derive(Clone, Debug)]
struct PorQ(Seq<Seq<usize>>);

#[cfg(test)]
#[derive(Clone, Debug, Default)]
struct UniPolynomial(Polyx);

#[cfg(test)]
impl Arbitrary for UniPolynomial {
    fn arbitrary(g: &mut quickcheck::Gen) -> UniPolynomial {
        let size = usize::arbitrary(g) % 20 + 1;
        let mut v: Vec<FpVesta> = vec![];
        for _ in 0..size {
            let new_val: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            v.push(new_val);
        }
        UniPolynomial(Seq::<FpVesta>::from_vec(v))
    }
}

#[cfg(test)]
impl Arbitrary for SeqOfUniPoly {
    fn arbitrary(g: &mut quickcheck::Gen) -> SeqOfUniPoly {
        let size = (usize::arbitrary(g) % 20 + 1); // min 1, max 100
        let mut seq_of_uni_poly = Seq::<Polyx>::create(size);
        for i in 0..size {
            let uni_poly = (UniPolynomial::arbitrary(g));
            seq_of_uni_poly[i] = uni_poly.0
        }
        SeqOfUniPoly(seq_of_uni_poly)
    }
}
#[cfg(test)]
fn gen_p(p_len: usize, p_i_max_len: usize) -> Seq<Seq<usize>> {
    let mut p: Seq<Seq<usize>> = Seq::<Seq<usize>>::create(p_len);
    for i in 0..p_len {
        let mut v: Vec<usize> = vec![];
        for j in 0..p_i_max_len {
            v.push(j);
        }
        v.shuffle(&mut thread_rng());
        let p_i_len: usize = rand::Rng::gen_range(&mut rand::thread_rng(), 0..p_i_max_len);

        let v: &[usize] = &v[0..p_i_len];
        p[i] = Seq::from_vec(v.to_vec());
    }
    p
}

#[cfg(test)]
impl Arbitrary for PorQ {
    fn arbitrary(g: &mut quickcheck::Gen) -> PorQ {
        let size = usize::arbitrary(g) % 20;
        let mut p_or_q: Seq<Seq<usize>> = Seq::<Seq<usize>>::create(size);
        for j in 0..size {
            let inner_size: usize = usize::arbitrary(g) % 20 + 3;
            let mut v: Vec<usize> = vec![];
            for i in 0..inner_size {
                let new_val: usize = usize::arbitrary(g);
                if !v.contains(&new_val) {
                    v.push(new_val);
                }
            }
            p_or_q[j] = Seq::<usize>::from_vec(v);
        }
        PorQ(p_or_q)
    }
}
#[cfg(test)]
#[derive(Clone, Debug)]
struct Points(Seq<(FpVesta, FpVesta)>);

#[cfg(test)]
impl Arbitrary for Points {
    fn arbitrary(g: &mut quickcheck::Gen) -> Points {
        let size = usize::arbitrary(g) % 20;
        let mut x_cords = vec![];
        let mut points = vec![];
        for _ in 0..size {
            let x: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            let y: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            if !x_cords.contains(&x) {
                points.push((x, y));
                x_cords.push(x)
            }
        }
        Points(Seq::<(FpVesta, FpVesta)>::from_vec(points))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct G1Container(G1_pallas);

#[cfg(test)]
impl Arbitrary for G1Container {
    fn arbitrary(g: &mut Gen) -> G1Container {
        let a = FpVesta::from_literal(u128::arbitrary(g));
        let generator = g1_generator_pallas();
        G1Container(g1mul_pallas(a, generator))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_step_5(h: UniPolynomial, n: usize) -> TestResult {
    let n = n % 100;

    if n < 2 {
        // discard if n is too small (step_5 requires a n>2 to make sense)
        return TestResult::discard();
    }
    let h = h.0;
    let n_g = h.len() / n + 2;

    let h = trim_polyx(h); // extract polynomial
    let h_parts = step_5(h.clone(), n, n_g); // split the h poly
    let n = n;

    let mut h_summed = Seq::<FpVesta>::create(1); // initialize a sum to the constant zero poly

    // h(x) = sum from 0 to n_g-2 (X^ni h_i(X))
    for i in 0..(n_g - 1) {
        let hi = h_parts[i].clone();
        let n_times_i = n * i;
        let Xni_times_hi = multi_poly_with_x_pow(hi, n_times_i);
        h_summed = add_polyx(h_summed, Xni_times_hi);
    }

    let h_summed = trim_polyx(h_summed);

    // assert the original and the summed polys have same length
    let h_len = h.len();
    let h_summed_len = h_summed.len();
    assert_eq!(
        h_len, h_summed_len,
        "lengths of h and h_summed mismatch: {} and {}\n h: {:?}\nh_summed: {:?}",
        h_len, h_summed_len, h, h_summed
    );

    // assert pairwise equality
    for i in 0..h.len() {
        assert_eq!(h[i], h_summed[i]);
    }

    TestResult::passed()
}

// Generators taken from:
// https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas
// (mina generator: (1,12418654782883325593414442427049395787963493412651469444558597405572177144507))
#[cfg(test)]
fn g1_generator_pallas() -> G1_pallas {
    (
        FpPallas::from_hex("1"),
        FpPallas::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        false,
    )
}

#[cfg(test)]
#[test]
fn test_step_5_6_7_8() {
    fn a(
        h: UniPolynomial,
        n: usize,
        x: usize,
        w: usize,
        randomness_seed: usize,
        G_seed: usize,
    ) -> bool {
        let h = h.0;

        // n should no be too small (for step 5)
        let n = n % 100 + 5;

        let n_g: usize = h.len() / n + 3;

        // STEP 5
        let h_s = step_5(h, n, n_g);

        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (W, G, x, commitment-randomness), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let x = FpVesta::from_literal(x as u128);
        let W = g1mul_pallas(FpVesta::from_literal(w as u128), g1_generator_pallas());

        // get the length of a h_i, which is the same as the length of G
        let h_i_len: &Polyx = &(h_s[usize::zero()]);
        let h_i_len = h_i_len.len();
        // get the number of h_i polys, which is the same as the number
        // of random elements for comitting
        let h_s_len = h_s.len();

        // there should be as many G elements as there are elements in the h_i polys
        let mut G = Seq::<G1_pallas>::create(h_i_len);
        let G_seed = FpVesta::from_literal(G_seed as u128 + 1); // +1, so it non-zero

        // create some "randomness" for G
        G[usize::zero()] = g1mul_pallas(G_seed, g1_generator_pallas());
        for i in 1..G.len() {
            G[i] = g1mul_pallas(G_seed, G[i - 1]);
        }

        // there should be as many random elements as there are h_i polys
        let mut h_blindings = Seq::<FpVesta>::create(h_s_len);
        // create some "randomness" for commitments
        h_blindings[usize::zero()] = FpVesta::from_literal(randomness_seed as u128 + 1); // +1, so it non-zero
        for i in 1..h_blindings.len() {
            h_blindings[i] = (h_blindings[i - 1] + FpVesta::ONE()) * FpVesta::TWO();
        }
        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////

        // STEP 6
        let H_s = step_6(h_s.clone(), &(G.clone(), W), h_blindings.clone());

        // STEP 7
        let H_prime = step_7(H_s, x, n);

        // STEP 8
        let (h_prime, h_prime_blinding) = step_8(h_s, x, n, h_blindings.clone());

        // sum the randomess corresponding (see the thesis for furhter explanation)
        let mut randomness_sum = FpVesta::ZERO();
        for i in 0..h_blindings.len() {
            let x_pow_ni = x.pow((n * (i)) as u128);
            randomness_sum = randomness_sum + (h_blindings[i] * x_pow_ni);
        }

        // commit to h_prime
        let h_prime_com = commit_polyx(&(G, W), h_prime, randomness_sum);
        assert_eq!(H_prime, h_prime_com);
        H_prime == h_prime_com
    }

    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(50).quickcheck(
        a as fn(
            h: UniPolynomial,
            n: usize,
            x: usize,
            w: usize,
            randomness_seed: usize,
            G_seed: usize,
        ) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_11() {
    fn a(
        n_a: usize,
        n_q: usize,
        x1: usize,
        x2: usize,
        R_power: usize,
        H_power: usize,
        a_seed: usize,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let mut n_a: usize = n_a % 100; // make it non-zero
        if n_a == 0 {
            n_a = 1;
        }
        let mut n_q: usize = n_q; // make it non-zero
        if n_q == 0 {
            n_q = 1;
        }
        if n_q > n_a {
            n_q = n_q % n_a
        }
        let x1 = FpVesta::from_literal(x1 as u128);
        let x2 = FpVesta::from_literal(x2 as u128);

        let H_prime = g1mul_pallas(
            FpVesta::from_literal(H_power as u128),
            g1_generator_pallas(),
        );
        let R = g1mul_pallas(
            FpVesta::from_literal(R_power as u128),
            g1_generator_pallas(),
        );

        let mut a = Seq::<G1_pallas>::create(n_a);
        a[usize::zero()] =
            g1mul_pallas(FpVesta::from_literal(a_seed as u128), g1_generator_pallas());
        for i in 1..a.len() {
            a[i] = g1mul_pallas(FpVesta::from_literal(a_seed as u128), a[i - 1]);
        }

        let mut sigma_list: Vec<usize> = vec![];
        let mut q = Seq::<Seq<usize>>::create(n_a);
        // create some random values for q, each entry with len n_q/2
        // and entries for sigma_list to be used in sigma
        // (note, here we actually do not guarantee that q's elements are distinct)
        // add one more entry for sigma_list, since the loop starts at 1
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx);
        q[usize::zero()] = Seq::<usize>::from_vec(vec![usize::zero()]); // q[usize::zero()]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<usize> = vec![];
            for j in 0..n_q {
                v.push(j);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..(n_q / 2)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx);
        }
        let n_q: usize = q.len();

        let sigma_seq = Seq::<usize>::from_vec(sigma_list);

        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////
        let (Q_s, x1, x2): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1,
            x2,
            H_prime,
            R,
            a.clone(),
            q.clone(),
            sigma_seq.clone(),
        );

        // calculate each Q_i and check that it corresponds with the output of step_11
        for i in 0..n_q {
            let mut Q = g1_default_pallas();
            // BULLET 1
            // Q_i := [x1]Q_i + A_j, for every time i is in some sigma(j)
            for j in 0..a.len() {
                let p_j = sigma(j, sigma_seq.clone(), q.clone());
                for k in 0..p_j.len() {
                    if i == p_j[k] {
                        Q = g1add_pallas(g1mul_pallas(x1, Q), a[j]);
                    }
                }
            }
            // BULLET 2
            // Q_0 := [x1^2]Q_0 + [x1]H' + R
            if i == 0 {
                Q = g1mul_pallas(x1.pow(2 as u128), Q);
                Q = g1add_pallas(Q, g1mul_pallas(x1, H_prime));
                Q = g1add_pallas(Q, R);
            }
            if Q != Q_s[i] {
                return false;
            }
        }

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(1).quickcheck(
        a as fn(
            n_a: usize,
            n_q: usize,
            x1: usize,
            x2: usize,
            R_power: usize,
            H_power: usize,
            a_seed: usize,
        ) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_12() {
    fn a(
        n_a: usize,
        n_q: usize,
        x1: usize,
        r: UniPolynomial,
        h: UniPolynomial,
        a_polys: SeqOfUniPoly,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let mut n_a: usize = n_a % 100; // make it non-zero
        if n_a == 0 {
            n_a = 1;
        }
        let mut n_q: usize = n_q; // make it non-zero
        if n_q == 0 {
            n_q = 1;
        }
        if n_q > n_a {
            n_q = n_q % n_a
        }
        let x1 = FpVesta::from_literal(x1 as u128);

        let mut sigma_list: Vec<usize> = vec![];
        let mut q = Seq::<Seq<usize>>::create(n_a);
        // create some random values for q, each entry with len n_q/2
        // and entries for sigma_list to be used in sigma
        // (note, here we actually do not guarantee that q's elements are distinct)
        // add one more entry for sigma_list, since the loop starts at 1
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx);
        q[usize::zero()] = Seq::<usize>::from_vec(vec![usize::zero()]); // q[usize::zero()]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<usize> = vec![];
            for j in 0..n_q {
                v.push(j);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..(n_q / 2)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx);
        }

        let sigma_seq = Seq::<usize>::from_vec(sigma_list);

        // a_polys is a number of random polys, but there should be n_a of them
        // (SeqOfUniPoly generates a fixed length seq of polys)
        let mut a_polys = a_polys.0;
        if a_polys.len() > n_a {
            a_polys = Seq::from_vec(a_polys.native_slice()[0..(n_a)].to_vec());
        } else if a_polys.len() < n_a {
            let diff = n_a - a_polys.len();
            for _ in 0..diff {
                // if wrong size, just use 0
                a_polys = a_polys.push(&Seq::<FpVesta>::from_vec(vec![FpVesta::ZERO()]));
            }
        }
        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////
        let h = h.0;
        let r = r.0;
        let (q_s, _) = step_12(
            n_a,
            x1,
            h.clone(),
            r.clone(),
            a_polys.clone(),
            q.clone(),
            sigma_seq.clone(),
            Seq::create(a_polys.len()), //
            FpVesta::ZERO(),            //
            FpVesta::ZERO(),            // we dont test blindess
        );
        // calculate each Q_i and check that it corresponds with the output of step_12
        for i in 0..n_q {
            let mut q_poly = Seq::<FpVesta>::create(1);
            // BULLET 1
            // q_i := x1 * q_i + a'_j(X), for every time i is in some sigma(j)
            for j in 0..n_a {
                let p_j = sigma(j, sigma_seq.clone(), q.clone());
                for k in 0..p_j.len() {
                    if i == p_j[k] as usize {
                        q_poly = add_polyx(mul_scalar_polyx(q_poly, x1), a_polys[j].clone())
                    }
                }
            }
            // BULLET 2
            // q_0 := x1^2 * q_0 + x1 * h'(X) + r(X)
            if i == 0 {
                q_poly = mul_scalar_polyx(q_poly, x1.pow(2 as u128));
                q_poly = add_polyx(q_poly, mul_scalar_polyx(h.clone(), x1));
                q_poly = add_polyx(q_poly, r.clone());
            }
            q_poly = trim_polyx(q_poly);
            let expected = trim_polyx(q_s[i].clone());
            if q_poly.len() != expected.len() {
                return false;
            }
            for j in 0..q_poly.len() {
                if q_poly[j] != expected[j] {
                    return false;
                }
            }
        }

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(10).quickcheck(
        a as fn(
            n_a: usize,
            n_q: usize,
            x1: usize,
            r: UniPolynomial,
            h: UniPolynomial,
            a_polys: SeqOfUniPoly,
        ) -> bool,
    );
}

// quickcheck is "limited" (not exactly) to eight arguments
// so we have to reuse some of the values in some way
#[cfg(test)]
#[test]
fn test_step_13() {
    fn a(
        n_q: usize,
        omega: usize,
        x: usize,
        r: usize,
        s: SeqOfUniPoly,
        g_prime: UniPolynomial,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let mut n_a: usize = s.0.len(); // make it non-zero
        if n_a == 0 {
            n_a = 1;
        }
        let mut n_q: usize = n_q; // make it non-zero
        if n_q == 0 {
            n_q = 1;
        }
        if n_q > n_a {
            n_q = n_q % n_a
        }
        let mut n = n_q * 3; // a bit of reuse, due the above restrictions
        if n == 0 {
            n = 1;
        }
        let omega = FpVesta::from_literal(omega as u128);
        let x = FpVesta::from_literal(x as u128);
        let x1 = x * FpVesta::TWO(); // a bit of reuse, due the above restrictions
        let r = FpVesta::from_literal(r as u128);
        let s = s.0;
        let mut q = Seq::<Seq<usize>>::create(n_a);
        let g_prime = g_prime.0;

        let mut sigma_list: Vec<usize> = vec![];
        let mut q = Seq::<Seq<usize>>::create(n_a);
        // create some random values for q, each entry with len n_q/2
        // and entries for sigma_list to be used in sigma
        // (note, here we actually do not guarantee that q's elements are distinct)
        // add one more entry for sigma_list, since the loop starts at 1
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx);
        q[usize::zero()] = Seq::<usize>::from_vec(vec![usize::zero()]); // q[usize::zero()]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<usize> = vec![];
            for j in 0..n_q {
                v.push(j);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..(n_q / 2)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx);
        }

        let sigma_seq = Seq::<usize>::from_vec(sigma_list);

        // s is a number of random polys, but there should be n_a of them
        // (SeqOfUniPoly generates a fixed length seq of polys)
        let mut s_polys = s;
        if s_polys.len() > n_a {
            s_polys = Seq::from_vec(s_polys.native_slice()[0..(n_a)].to_vec());
        } else if s_polys.len() < n_a {
            let diff = n_a - s_polys.len();
            for _ in 0..diff {
                // if wrong size, just use 0
                s_polys = s_polys.push(&Seq::<FpVesta>::from_vec(vec![FpVesta::ZERO()]));
            }
        }

        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////
        let (r_s, _) = step_13(
            n,
            omega,
            x,
            x1,
            r,
            s_polys.clone(),
            q.clone(),
            sigma_seq.clone(),
            eval_polyx(g_prime.clone(), x),
            g_prime.clone(),
        );

        // calculate each r_i and check that it corresponds with the output of step_13
        for i in 0..n_q {
            let mut r_poly = Seq::<FpVesta>::create(1);
            // BULLET 1
            // r_i := x1 * r_i + s_j(X), for every time i is in some sigma(j)
            for j in 0..n_a {
                let p_j = sigma(j, sigma_seq.clone(), q.clone());
                for k in 0..p_j.len() {
                    if i == p_j[k] {
                        r_poly = add_polyx(mul_scalar_polyx(r_poly, x1), s_polys[j].clone())
                    }
                }
            }
            // BULLET 2
            // r_0 := x1^2 * r_0 + x1 * h + r
            if i == 0 {
                r_poly = mul_scalar_polyx(r_poly, x1.pow(2 as u128));

                // calculate h
                let g_prime_x: FpVesta = eval_polyx(g_prime.clone(), x);
                let vanishing_poly: Polyx = compute_vanishing_polynomial(omega, n);
                let vanishing_poly_x: FpVesta = eval_polyx(vanishing_poly, x);
                let h = g_prime_x / vanishing_poly_x;

                r_poly = add_scalar_polyx(r_poly, x1 * h);
                r_poly = add_scalar_polyx(r_poly, r.clone());
            }
            r_poly = trim_polyx(r_poly);
            let expected = trim_polyx(r_s[i].clone());
            if r_poly.len() != expected.len() {
                return false;
            }
            for j in 0..r_poly.len() {
                if r_poly[j] != expected[j] {
                    return false;
                }
            }
        }

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            n_q: usize,
            omega: usize,
            x: usize,
            r: usize,
            s: SeqOfUniPoly,
            g_prime: UniPolynomial,
        ) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_14() {
    fn a(
        w: usize,
        x: usize,
        q_polys: SeqOfUniPoly,
        r_polys: SeqOfUniPoly,
        r: usize,
        omega: usize,
        G_seed: usize,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let W = g1mul_pallas(FpVesta::from_literal(w as u128), g1_generator_pallas());

        let x = FpVesta::from_literal(x as u128);

        let x2 = x.mul(x.add(FpVesta::TWO().pow(19 as u128)));

        let omega: FpVesta = FpVesta::TWO();

        let r_polys = r_polys.0;
        let q_polys = q_polys.0;

        let r = FpVesta::from_literal(r as u128);
        let mut n_q = q_polys.len();
        if n_q > r_polys.len() {
            n_q = r_polys.len()
        }

        // create some random values for q, each entry with len n_q/2
        let mut sigma_list: Vec<usize> = vec![];
        let mut q = Seq::<Seq<usize>>::create(n_q);
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx);
        q[usize::zero()] = Seq::<usize>::from_vec(vec![usize::zero()]); // q[usize::zero()]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<usize> = vec![];
            for j in 0..n_q {
                v.push(j);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..(n_q / 2)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx);
        }

        let sigma_seq = Seq::<usize>::from_vec(sigma_list);

        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////

        //////////////////////////////////////////////////////////////////////////////////
        /// MANUEL CALCULATION
        //////////////////////////////////////////////////////////////////////////////////
        let mut sum_result = Seq::from_vec(vec![FpVesta::from_literal(0 as u128)]);

        for i in 0..n_q {
            let dividend_lhs: Polyx =
                mul_scalar_polyx(q_polys[i].clone(), x2.pow((n_q - i - 1) as u128));
            let dividend_rhs: Polyx =
                mul_scalar_polyx(r_polys[i].clone(), x2.pow((n_q - i - 1) as u128));
            let dividend: Polyx = sub_polyx(dividend_lhs, dividend_rhs);

            let q_i = q[i].clone();
            let n_e = q_i.len();
            // let mut divisor: Seq<Fp> = Seq::from_vec(vec![FpVesta::from_literal(1 as u128)]);
            let mut divisor: Polyx = Seq::<FpVesta>::create(q_i.len() + 1);
            divisor[usize::zero()] = FpVesta::ONE();

            for j in 0..n_e {
                let divisor_lhs: Polyx = multi_poly_with_x(divisor.clone());
                let q_i_j: usize = q_i[j];
                let rhs_scalar: FpVesta = omega.pow(q_i_j as u128).mul(x).neg();
                let divisor_rhs_mult: Polyx = mul_scalar_polyx(divisor, rhs_scalar);
                divisor = add_polyx(divisor_lhs, divisor_rhs_mult);
            }
            let division: Polyx = divide_polyx(dividend.clone(), divisor).0;

            sum_result = add_polyx(sum_result, division);
        }

        //////////////////////////////
        /// CREATE G WITH CORRECT LENGTH - NEEDS TO BE SAME LENGTH AS POLY YOU WANT TO COMMIT TO
        //////////////////////////////
        let mut G = Seq::<G1_pallas>::create(sum_result.clone().len());
        let G_seed = FpVesta::from_literal(G_seed as u128 + 1); // +1, so it non-zero

        // create some "randomness" for G
        G[usize::zero()] = g1mul_pallas(G_seed, g1_generator_pallas());
        for i in 1..G.len() {
            G[i] = g1mul_pallas(G_seed, G[i - 1]);
        }
        /////////////////////////////
        /// FINISHED CREATHING G
        /////////////////////////////
        let q_prime_test = commit_polyx(&(G.clone(), W), sum_result, r);
        // we ignore the blinding and polynomial
        let (Q_prime, _, _) = step_14(
            &(G.clone(), W),
            x2,
            q_polys.clone(),
            r_polys.clone(),
            q.clone(),
            r,
            omega,
            x,
        );

        assert_eq!(Q_prime, q_prime_test);
        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            w: usize,
            x: usize,
            q_polys: SeqOfUniPoly,
            r_polys: SeqOfUniPoly,
            r: usize,
            omega: usize,
            G_seed: usize,
        ) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_16() {
    fn a(x3: usize, q_polys: SeqOfUniPoly) -> bool {
        let q_polys: Seq<Polyx> = q_polys.0;
        let n_q: usize = q_polys.len();
        let x3: FpVesta = FpVesta::from_literal(x3 as u128);
        let u: Polyx = step_16(n_q, x3, q_polys.clone());
        for i in 0..u.len() {
            let u_i: FpVesta = u[i];
            let q_i: Polyx = q_polys[i].clone();
            let q_i_eval: FpVesta = eval_polyx(q_i, x3);
            assert_eq!(u_i, q_i_eval);
        }
        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(x3: usize, q_polys: SeqOfUniPoly) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_18() {
    fn a(rnd1: usize, rnd2: usize, omega: usize, r: SeqOfUniPoly) -> bool {
        let r: Seq<Polyx> = r.0;
        let n_q: usize = r.len();
        let mut x1: FpVesta = FpVesta::from_literal(rnd1 as u128).pow(123 as u128);
        if x1 == FpVesta::ZERO() {
            x1 = FpVesta::ONE()
        }
        let mut x2: FpVesta = x1.pow(rnd1 as u128);
        if x2 == FpVesta::ZERO() {
            x2 = FpVesta::ONE()
        }
        let mut x3: FpVesta = x2 + x1 + FpVesta::from_literal(rnd2 as u128 + 7).pow(42 as u128);
        if x3 == FpVesta::ZERO() {
            x3 = FpVesta::ONE()
        }
        let mut x4: FpVesta = x1 * x2 + FpVesta::from_literal(929299292 as u128);
        if x4 == FpVesta::ZERO() {
            x4 = FpVesta::ONE()
        }
        let mut x: FpVesta = FpVesta::from_literal(rnd1 as u128);
        if x == FpVesta::ZERO() {
            x = FpVesta::ONE()
        }
        let mut omega: FpVesta = FpVesta::from_literal(omega as u128);
        if omega == FpVesta::ZERO() {
            omega = FpVesta::from_literal(123 as u128)
        }
        let Q_prime: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(rnd2 as u128), g1_generator_pallas());
        let mut Q: Seq<(FpPallas, FpPallas, bool)> = Seq::<G1_pallas>::create(n_q);
        for i in 0..n_q {
            let g1_seed: FpVesta =
                FpVesta::from_literal((rnd1 % (i + 1)) as u128).pow(rnd2 as u128);
            Q[i] = g1mul_pallas(g1_seed, g1_generator_pallas());
        }
        let mut u: Polyx = Seq::<FpVesta>::create(n_q);
        for i in 0..n_q {
            let random_Fp: FpVesta =
                FpVesta::from_literal((rnd2 % (i + 1)) as u128).pow(rnd1 as u128);
            u[i] = random_Fp;
        }

        let mut sigma_list: Vec<usize> = vec![];
        let mut q: Seq<Seq<usize>> = Seq::<Seq<usize>>::create(n_q);
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx);
        q[usize::zero()] = Seq::<usize>::from_vec(vec![usize::zero()]); // q[usize::zero()]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<usize> = vec![];
            for j in 0..n_q {
                v.push(j);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..(n_q / 2)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx);
        }

        let sigma_seq = Seq::<usize>::from_vec(sigma_list);

        let (P, v) = step_18(
            x,
            x1,
            x2,
            x3,
            x4,
            omega,
            Q_prime,
            Q.clone(),
            u.clone(),
            r.clone(),
            q.clone(),
        );

        ///////////TEST IMPLEMENTATION FOR P////////////////////
        let mut test_P: G1_pallas = g1mul_pallas(x4.pow(n_q as u128), Q_prime);
        for i in 0..n_q {
            test_P = g1add_pallas(test_P, g1mul_pallas(x4.pow((n_q - 1 - i) as u128), Q[i]));
        }
        assert_eq!(P, test_P);
        ////////////TEST IMPLEMENTATION FOR v//////////////////
        let mut test_v = FpVesta::ZERO();
        // let mut second_sum: Fp = FpVesta::ZERO();
        let mut first_sum: FpVesta = FpVesta::ZERO();
        let mut second_sum: FpVesta = FpVesta::ZERO();
        for i in 0..n_q {
            let first_sum_dividend: FpVesta =
                x2.pow((n_q - 1 - i) as u128) * (u[i] - eval_polyx(r[i].clone(), x3));
            let q_i = q[i].clone();
            let mut first_sum_divisor = FpVesta::ONE();
            for j in 0..q_i.len() {
                first_sum_divisor = first_sum_divisor * (x3 - omega.pow(q_i[j] as u128) * x);
            }
            second_sum = second_sum + x4.pow((n_q - 1 - i) as u128) * u[i];
            first_sum = first_sum + (first_sum_dividend / first_sum_divisor);
        }
        first_sum = first_sum * x4.pow(n_q as u128);
        let test_v: FpVesta = first_sum + second_sum;

        assert_eq!(v, test_v);

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new()
        .tests(5)
        .quickcheck(a as fn(rnd1: usize, rnd2: usize, omega: usize, r: SeqOfUniPoly) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_19() {
    fn a(x4: usize, q_prime: UniPolynomial, q_polys: SeqOfUniPoly) -> bool {
        let q_polys: Seq<Polyx> = q_polys.0;
        let n_q: usize = q_polys.len();
        let x4: FpVesta = FpVesta::from_literal(x4 as u128);
        let x4nq: FpVesta = x4.pow(n_q as u128);
        let mut q_prime: Polyx = q_prime.0;
        // ignores blindness
        let (p, _) = step_19(
            x4,
            q_prime.clone(),
            q_polys.clone(),
            Seq::create(q_polys.len()),
            FpVesta::ZERO(),
        );
        q_prime = mul_scalar_polyx(q_prime, x4nq);

        for i in 0..q_polys.len() {
            let mut q_i: Polyx = q_polys[i].clone();
            q_i = mul_scalar_polyx(q_i, x4.pow((n_q - 1 - i) as u128));
            // q_i = mul_scalar_polyx(q_i, x4);
            q_prime = add_polyx(q_i, q_prime.clone());
        }
        assert_eq!(p.len(), q_prime.len());
        for j in 0..p.len() {
            assert_eq!(p[j], q_prime[j]);
        }
        true
    }
    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(x4: usize, q_prime: UniPolynomial, q_polys: SeqOfUniPoly) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_22() {
    fn a(p_val: usize, g0_val: usize, s_val: usize, v_val: usize, xi_val: usize) -> bool {
        let p: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(p_val as u128), g1_generator_pallas());
        let g0: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(g0_val as u128), g1_generator_pallas());
        let s: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(s_val as u128), g1_generator_pallas());
        let v: FpVesta = FpVesta::from_literal(v_val as u128);
        let xi: FpVesta = FpVesta::from_literal(xi_val as u128);

        let test_result: G1_pallas = g1add_pallas(
            p,
            g1add_pallas(g1neg_pallas(g1mul_pallas(v, g0)), g1mul_pallas(xi, s)),
        );

        let p_prime: G1_pallas = step_22(p, g0, s, v, xi);

        assert_eq!(p_prime, test_result);

        true
    }

    QuickCheck::new().tests(50).quickcheck(
        a as fn(p_val: usize, g0_val: usize, s_val: usize, v_val: usize, xi_val: usize) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_23() {
    fn a(p: UniPolynomial, s: UniPolynomial, x3: usize, xi: usize) -> bool {
        let p: Polyx = p.0;
        let s: Polyx = s.0;
        let x3: FpVesta = FpVesta::from_literal(x3 as u128);
        let xi: FpVesta = FpVesta::from_literal(xi as u128);
        let test_result = add_polyx(
            add_scalar_polyx(p.clone(), eval_polyx(p.clone(), x3).neg()),
            mul_scalar_polyx(s.clone(), xi),
        );
        // ignore blindess
        let (p_prime, _) = step_23(p, s, x3, xi, FpVesta::ZERO(), FpVesta::ZERO());
        assert_eq!(p_prime.len(), test_result.len());
        for i in 0..p_prime.len() {
            assert_eq!(p_prime[i], test_result[i])
        }
        true
    }
    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(p: UniPolynomial, s: UniPolynomial, x3: usize, xi: usize) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_24() {
    use hacspec_lib::num::traits::Pow;
    let p_prime_poly: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(12398129 as u128),
        FpVesta::from_literal(2222 as u128),
        FpVesta::from_literal(3038300 as u128),
        FpVesta::from_literal(4 as u128),
    ]);
    let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
        g1mul_pallas(FpVesta::from_literal(2123 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(30283 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(4 as u128), g1_generator_pallas()),
        g1mul_pallas(
            FpVesta::from_literal(999999999999 as u128),
            g1_generator_pallas(),
        ),
    ]);
    let x3: FpVesta = FpVesta::from_literal(981298129832983298 as u128);
    let z: FpVesta = FpVesta::from_literal(9812398329834298123123 as u128);
    let U: G1_pallas = g1mul_pallas(FpVesta::from_literal(99 as u128), g1_generator_pallas());
    let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(42 as u128), g1_generator_pallas());
    let k = 2;
    let n = 2.exp(2) as usize;
    let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(298398123 as u128),
        FpVesta::from_literal(3232323 as u128),
    ]);
    let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(939 as u128),
        FpVesta::from_literal(10293 as u128),
    ]);
    let mut L: Seq<G1_pallas> = Seq::<G1_pallas>::create(k);
    let mut R: Seq<G1_pallas> = Seq::<G1_pallas>::create(k);

    let u: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(1 as u128),
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(3 as u128),
        FpVesta::from_literal(4 as u128),
    ]);
    // ignore blindness
    let (real_p_prime, real_G_prime, real_b, real_L, real_R, _, _) = step_24(
        p_prime_poly.clone(),
        G.clone(),
        x3,
        z,
        U,
        W,
        n,
        k,
        u.clone(),
        L_blinding.clone(),
        R_blinding.clone(),
    );

    ////////manuel calculation////////////////
    let mut G_prime: Seq<G1_pallas> = G.clone();

    //First round
    let p_prime_lo: Polyx =
        Seq::<FpVesta>::from_vec(vec![p_prime_poly[usize::zero()], p_prime_poly[1]]);
    let p_prime_hi: Polyx = Seq::<FpVesta>::from_vec(vec![p_prime_poly[2], p_prime_poly[3]]);
    let G_prime_lo: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![G[usize::zero()], G[1]]);
    let G_prime_hi: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![G[2], G[3]]);
    let b_lo: Polyx = Seq::<FpVesta>::from_vec(vec![x3.pow(0 as u128), x3.pow(1 as u128)]);
    let b_hi: Polyx = Seq::<FpVesta>::from_vec(vec![x3.pow(2 as u128), x3.pow(3 as u128)]);
    let L_0: G1_pallas = g1add_pallas(
        g1add_pallas(
            msm(p_prime_hi.clone(), G_prime_lo.clone()),
            g1mul_pallas(z * inner_product(p_prime_hi.clone(), b_lo.clone()), U),
        ),
        g1mul_pallas(L_blinding[usize::zero()], W),
    );
    L[usize::zero()] = L_0;

    let R_0: G1_pallas = g1add_pallas(
        g1add_pallas(
            msm(p_prime_lo.clone(), G_prime_hi.clone()),
            g1mul_pallas(z * inner_product(p_prime_lo.clone(), b_hi.clone()), U),
        ),
        g1mul_pallas(R_blinding[usize::zero()], W),
    );
    R[usize::zero()] = R_0;

    G_prime = Seq::<G1_pallas>::from_vec(vec![
        g1add_pallas(
            G_prime_lo[usize::zero()],
            g1mul_pallas(u[usize::zero()], G_prime_hi[usize::zero()]),
        ),
        g1add_pallas(G_prime_lo[1], g1mul_pallas(u[usize::zero()], G_prime_hi[1])),
    ]);
    let mut b: Polyx = Seq::<FpVesta>::from_vec(vec![
        b_lo[usize::zero()] + u[usize::zero()] * b_hi[usize::zero()],
        b_lo[1] + u[usize::zero()] * b_hi[1],
    ]);
    let u_j: FpVesta = u[usize::zero()];
    let mut p_prime: Polyx = Seq::<FpVesta>::from_vec(vec![
        p_prime_lo[usize::zero()] + u_j.inv() * p_prime_hi[usize::zero()],
        p_prime_lo[1] + u_j.inv() * p_prime_hi[1],
    ]);

    //second round
    let p_prime_lo: Polyx = Seq::<FpVesta>::from_vec(vec![p_prime[usize::zero()]]);
    let p_prime_hi: Polyx = Seq::<FpVesta>::from_vec(vec![p_prime[1]]);
    let G_prime_lo: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![G_prime[usize::zero()]]);
    let G_prime_hi: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![G_prime[1]]);
    let b_lo: Polyx = Seq::<FpVesta>::from_vec(vec![b[usize::zero()]]);
    let b_hi: Polyx = Seq::<FpVesta>::from_vec(vec![b[1]]);
    let L_1: G1_pallas = g1add_pallas(
        g1add_pallas(
            msm(p_prime_hi.clone(), G_prime_lo.clone()),
            g1mul_pallas(z * inner_product(p_prime_hi.clone(), b_lo.clone()), U),
        ),
        g1mul_pallas(L_blinding[1], W),
    );
    L[1] = L_1;

    let R_1: G1_pallas = g1add_pallas(
        g1add_pallas(
            msm(p_prime_lo.clone(), G_prime_hi.clone()),
            g1mul_pallas(z * inner_product(p_prime_lo.clone(), b_hi.clone()), U),
        ),
        g1mul_pallas(R_blinding[1], W),
    );
    R[1] = R_1;

    G_prime = Seq::<G1_pallas>::from_vec(vec![g1add_pallas(
        G_prime_lo[usize::zero()],
        g1mul_pallas(u[1], G_prime_hi[usize::zero()]),
    )]);
    b = Seq::<FpVesta>::from_vec(vec![
        b_lo[usize::zero()] + u[usize::zero()] * b_hi[usize::zero()],
    ]);
    let u_j: FpVesta = u[1];

    p_prime = Seq::<FpVesta>::from_vec(vec![
        p_prime_lo[usize::zero()] + u_j.inv() * p_prime_hi[usize::zero()],
    ]);
    assert_eq!(G_prime[usize::zero()], real_G_prime[usize::zero()]);
    assert_eq!(p_prime[usize::zero()], real_p_prime[usize::zero()]);
    assert_eq!(L[usize::zero()], real_L[usize::zero()]);
    assert_eq!(L[1], real_L[1]);
    assert_eq!(R[usize::zero()], real_R[usize::zero()]);
    assert_eq!(R[1], real_R[1]);
}

#[cfg(test)]
#[test]
fn test_step_26() {
    let u: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(743 as u128),
        FpVesta::from_literal(9 as u128),
    ]);
    let L: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
        g1mul_pallas(FpVesta::from_literal(74 as u128), g1_generator_pallas()),
        g1mul_pallas(
            FpVesta::from_literal(749292992 as u128),
            g1_generator_pallas(),
        ),
    ]);
    let R: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
        g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
        g1mul_pallas(
            FpVesta::from_literal(92929929292 as u128),
            g1_generator_pallas(),
        ),
    ]);

    let P_prime: G1_pallas = g1mul_pallas(
        FpVesta::from_literal(1239734 as u128),
        g1_generator_pallas(),
    );
    let c: FpVesta = FpVesta::from_literal(1919191 as u128);
    let G_prime_0: G1_pallas = g1mul_pallas(
        FpVesta::from_literal(9191203983123123123123 as u128),
        g1_generator_pallas(),
    );
    let b_0: FpVesta = FpVesta::from_literal(87410923091283 as u128);
    let z: FpVesta = FpVesta::from_literal(699388299374 as u128);
    let U: G1_pallas = g1mul_pallas(
        FpVesta::from_literal(77777777 as u128),
        g1_generator_pallas(),
    );
    let f: FpVesta = FpVesta::ONE();
    let W: G1_pallas = (
        FpPallas::from_hex("29A35E837F1BC8F4D83DD8E452DAC6691BDEDE5F0916BB02E7EB3BF0D8724746"),
        FpPallas::from_hex("2E7E5A3C4EFBE72E130E31E28F22E98BF0A3225FCB5E579B61B98F28083A8A05"),
        false,
    );

    let mut rhs: G1_pallas = g1add_pallas(
        g1mul_pallas(FpVesta::from_literal(743 as u128).inv(), L[usize::zero()]),
        g1mul_pallas(FpVesta::from_literal(9 as u128).inv(), L[1]),
    );
    rhs = g1add_pallas(rhs, P_prime);
    rhs = g1add_pallas(
        rhs,
        g1add_pallas(
            g1mul_pallas(FpVesta::from_literal(743 as u128), R[usize::zero()]),
            g1mul_pallas(FpVesta::from_literal(9 as u128), R[1]),
        ),
    );
    let mut lhs: G1_pallas = g1mul_pallas(c, G_prime_0);
    lhs = g1add_pallas(lhs, g1mul_pallas((c * b_0 * z), U));
    lhs = g1add_pallas(lhs, g1mul_pallas(f, W));
    let diff: G1_pallas = g1add_pallas(rhs, g1neg_pallas(lhs));
    assert!(step_26(u, L, P_prime, R, c, G_prime_0, b_0, z, U, f, W))
}

#[cfg(test)]
#[test]
fn test_step_11_12() {
    fn a(
        a0_0: usize,
        a0_2: usize,
        a1_0: usize,
        a1_2: usize,
        a2_0: usize,
        a2_2: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a0_0 as u128)),
            (
                omega.pow(1 as u128),
                FpVesta::from_literal(a0_0 as u128)
                    + FpVesta::from_literal(a1_0 as u128)
                    + FpVesta::from_literal(a2_0 as u128),
            ),
            (omega.pow(2 as u128), FpVesta::from_literal(a0_2 as u128)),
            (
                omega.pow(3 as u128),
                FpVesta::from_literal(a0_2 as u128)
                    + FpVesta::from_literal(a1_2 as u128)
                    + FpVesta::from_literal(a2_2 as u128),
            ),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a1_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a1_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a2_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a2_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add);

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(3 as u128),
            FpVesta::from_literal(4523 as u128),
            FpVesta::from_literal(838 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        for i in 0..Q_is.len() {
            let Q = Q_is[i];
            let q = q_is[i].clone();
            let q_blind = q_blinds[i];
            let q_commit = commit_polyx(&crs, q.clone(), q_blind);
            if Q != q_commit {
                eprintln!(
                    "Q and commitment for q mismatch, Q: {:?}, q: {:?}, q_blind: {:?}, q commit: {:?}",
                    Q, q, q_blind, q_commit
                );
                return TestResult::failed();
            }
        }

        TestResult::passed()
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            a0_0: usize,
            a0_2: usize,
            a1_0: usize,
            a1_2: usize,
            a2_0: usize,
            a2_2: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn test_step_18_19() {
    fn a(
        a0_0: usize,
        a0_2: usize,
        a1_0: usize,
        a1_2: usize,
        a2_0: usize,
        a2_2: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a0_0 as u128)),
            (
                omega.pow(1 as u128),
                FpVesta::from_literal(a0_0 as u128)
                    + FpVesta::from_literal(a1_0 as u128)
                    + FpVesta::from_literal(a2_0 as u128),
            ),
            (omega.pow(2 as u128), FpVesta::from_literal(a0_2 as u128)),
            (
                omega.pow(3 as u128),
                FpVesta::from_literal(a0_2 as u128)
                    + FpVesta::from_literal(a1_2 as u128)
                    + FpVesta::from_literal(a2_2 as u128),
            ),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a1_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a1_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a2_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a2_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add.clone());

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(3 as u128),
            FpVesta::from_literal(4523 as u128),
            FpVesta::from_literal(838 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
        let fat_a_1: &Seq<FpVesta> = &fat_a[1];
        let fat_a_2: &Seq<FpVesta> = &fat_a[2];
        // recreate g'(x) from **a**
        let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
            * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()]
                - fat_a_0[1]);

        let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
            n,
            omega,
            x_challenge,
            x1_challenge,
            r,
            s_is,
            q.clone(),
            sigma_list.clone(),
            g_prime_eval_combined_from_a,
            g_prime,
        );

        let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
        let (Q_prime, q_prime, Q_prime_blind) = step_14(
            &crs,
            x2_challenge,
            q_is.clone(),
            r_is_prover,
            q.clone(),
            step14_blinding,
            omega,
            x_challenge,
        );

        let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

        let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

        let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

        let (P, v) = step_18(
            x_challenge,
            x1_challenge,
            x2_challenge,
            x3_challenge,
            x4_challenge,
            omega,
            Q_prime,
            Q_is,
            u.clone(),
            r_is_verifier,
            q,
        );

        let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

        let p_commit = commit_polyx(&crs, p_poly, p_blind);

        if P == p_commit {
            TestResult::passed()
        } else {
            eprintln!(
                "P and commitment for p mismatch, P: {:?}, p: {:?}, p_blind: {:?}, p commit: {:?}",
                P, p, p_blind, p_commit
            );
            TestResult::failed()
        }
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            a0_0: usize,
            a0_2: usize,
            a1_0: usize,
            a1_2: usize,
            a2_0: usize,
            a2_2: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn test_step_22_23() {
    fn a(
        a0_0: usize,
        a0_2: usize,
        a1_0: usize,
        a1_2: usize,
        a2_0: usize,
        a2_2: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a0_0 as u128)),
            (
                omega.pow(1 as u128),
                FpVesta::from_literal(a0_0 as u128)
                    + FpVesta::from_literal(a1_0 as u128)
                    + FpVesta::from_literal(a2_0 as u128),
            ),
            (omega.pow(2 as u128), FpVesta::from_literal(a0_2 as u128)),
            (
                omega.pow(3 as u128),
                FpVesta::from_literal(a0_2 as u128)
                    + FpVesta::from_literal(a1_2 as u128)
                    + FpVesta::from_literal(a2_2 as u128),
            ),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a1_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a1_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a2_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a2_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add.clone());

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(3 as u128),
            FpVesta::from_literal(4523 as u128),
            FpVesta::from_literal(838 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
        let fat_a_1: &Seq<FpVesta> = &fat_a[1];
        let fat_a_2: &Seq<FpVesta> = &fat_a[2];
        // recreate g'(x) from **a**
        let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
            * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()]
                - fat_a_0[1]);

        let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
            n,
            omega,
            x_challenge,
            x1_challenge,
            r,
            s_is,
            q.clone(),
            sigma_list.clone(),
            g_prime_eval_combined_from_a,
            g_prime,
        );

        let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
        let (Q_prime, q_prime, Q_prime_blind) = step_14(
            &crs,
            x2_challenge,
            q_is.clone(),
            r_is_prover,
            q.clone(),
            step14_blinding,
            omega,
            x_challenge,
        );

        let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

        let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

        let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

        let (P, v) = step_18(
            x_challenge,
            x1_challenge,
            x2_challenge,
            x3_challenge,
            x4_challenge,
            omega,
            Q_prime,
            Q_is,
            u.clone(),
            r_is_verifier,
            q,
        );

        let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

        let step20_blinding: FpVesta = FpVesta::from_literal(532 as u128);
        let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
            (
                FpVesta::from_literal(729 as u128),
                FpVesta::from_literal(23 as u128),
            ),
            (
                FpVesta::from_literal(73 as u128),
                FpVesta::from_literal(102 as u128),
            ),
            (
                FpVesta::from_literal(444 as u128),
                FpVesta::from_literal(484 as u128),
            ),
            (x3_challenge, FpVesta::ZERO()),
        ]);
        let s_poly: Polyx = lagrange_polyx(s_poly_points);

        let (S, s_blind) = step_20(s_poly.clone(), crs.clone(), step20_blinding);

        let (xi, z) = step_21(
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        );

        let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

        let (p_prime_poly, p_prime_blind) =
            step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

        let p_prime_commit = commit_polyx(&crs, p_prime_poly.clone(), p_prime_blind);

        if P_prime == p_prime_commit {
            TestResult::passed()
        } else {
            eprintln!(
                "P_prime and commitment for p_prime mismatch, P_prime: {:?}, p_prime: {:?}, p_prime_blind: {:?}, p_prime commit: {:?}",
                P_prime, p_prime_poly, p_prime_blind, p_prime_commit
            );
            TestResult::failed()
        }
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            a0_0: usize,
            a0_2: usize,
            a1_0: usize,
            a1_2: usize,
            a2_0: usize,
            a2_2: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn testmsm() {
    let fs1 = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(144 as u128),
        FpVesta::from_literal(22 as u128),
        FpVesta::from_literal(3 as u128),
        FpVesta::from_literal(74 as u128),
        FpVesta::from_literal(79 as u128),
    ]);

    let fs2 = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(112 as u128),
        FpVesta::from_literal(2231 as u128),
        FpVesta::from_literal(88 as u128),
        FpVesta::from_literal(9 as u128),
        FpVesta::from_literal(98 as u128),
    ]);
    let gs = Seq::<G1_pallas>::from_vec(vec![
        (
            FpPallas::from_literal(2 as u128),
            FpPallas::from_literal(2 as u128),
            false,
        ),
        (
            FpPallas::from_literal(2 as u128),
            FpPallas::from_literal(5 as u128),
            false,
        ),
        (
            FpPallas::from_literal(5 as u128),
            FpPallas::from_literal(3 as u128),
            false,
        ),
        (
            FpPallas::from_literal(6 as u128),
            FpPallas::from_literal(8 as u128),
            false,
        ),
        (
            FpPallas::from_literal(2 as u128),
            FpPallas::from_literal(5 as u128),
            false,
        ),
    ]);
    let msmed1 = msm(fs1.clone(), gs.clone());
    let msmed2 = msm(fs2.clone(), gs.clone());
    let msm_sum = g1add_pallas(msmed1, msmed2);
    let mut fs_sum = add_polyx(fs1, fs2);
    let sum_sum = msm(fs_sum, gs);
}

#[cfg(test)]
#[quickcheck]
fn test_step_9(r_poly: UniPolynomial, a_prime_seq: SeqOfUniPoly, x: usize, omega: usize) {
    let r_poly = r_poly.0;
    let x = FpVesta::from_literal(x as u128);
    let omega = FpVesta::from_literal(omega as u128);
    let a_prime_seq = a_prime_seq.0;
    let p = gen_p(a_prime_seq.len(), 20);
    let (r, a) = step_9(r_poly.clone(), a_prime_seq.clone(), omega, p.clone(), x);
    for i in 0..a.len() {
        let a_i = a[i].clone();
        let a_prime_i = a_prime_seq[i].clone();
        let p_i = p[i].clone();
        for j in 0..a_i.len() {
            let a_i_j = a_i[j];
            let p_i_j = p_i[j];
            let eval = eval_polyx(a_prime_i.clone(), omega.pow(p_i_j as u128) * x);
            assert_eq!(a_i_j, eval);
        }
    }
    assert_eq!(r, eval_polyx(r_poly, x));
}

#[cfg(test)]
#[test]
fn test_step_9_10() {
    fn a(a_prime_seq: SeqOfUniPoly, omega_value: usize, x_value: usize) -> TestResult {
        let mut x_value: usize = x_value;
        let mut omega_value: usize = omega_value;
        if x_value < 2 {
            x_value = x_value + 2;
        }
        if omega_value < 3 {
            omega_value = omega_value + 3;
        }
        let a_prime_seq = a_prime_seq.0;
        let p = gen_p(a_prime_seq.len(), 50);

        let r = Seq::<FpVesta>::from_vec(vec![FpVesta::ZERO()]);

        let omega: FpVesta = FpVesta::from_literal(omega_value as u128);
        let x: FpVesta = FpVesta::from_literal(x_value as u128);

        let p: Seq<Seq<usize>> = p;
        let n_a: usize = a_prime_seq.len();
        if x_value < 2 {
            x_value = x_value + 2;
        }
        if omega_value < 3 {
            omega_value = omega_value + 3;
        }
        let (_, a) = step_9(r, a_prime_seq, omega, p.clone(), x);
        let s = step_10(omega, p.clone(), x, a.clone());

        for i in 0..n_a {
            let p_i: Seq<usize> = p[i].clone();
            let s_i: Polyx = s[i].clone();
            let a_i: Polyx = a[i].clone();
            let n_e = p_i.len();
            for j in 0..n_e {
                let p_i_j = p_i[j];
                let function_arg: FpVesta = omega.pow(p_i_j as u128) * x;
                let s_eval: FpVesta = eval_polyx(s_i.clone(), function_arg);
                let a_i_j: FpVesta = a_i[j];
                assert_eq!(s_eval, a_i_j);
            }
        }

        TestResult::passed()
    }
    QuickCheck::new().tests(1).quickcheck(
        a as fn(a_prime_seq: SeqOfUniPoly, omega_value: usize, x_value: usize) -> TestResult,
    );
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_x(a: UniPolynomial) {
    // TODO not sure this should stay?
    let p1 = a.0;
    let new_p = &multi_poly_with_x(p1.clone());
    for i in 1..new_p.len() {
        assert_eq!(new_p[i], p1[i - 1]);
    }
    assert_eq!(new_p[usize::zero()], FpVesta::from_literal(0 as u128));
}

#[cfg(test)]
#[test]
fn test_commit_to_poly_parts() {
    let crs: CRS = (
        Seq::<G1_pallas>::from_vec(vec![
            g1_default_pallas(),
            g1_default_pallas(),
            g1_default_pallas(),
        ]),
        g1_default_pallas(),
    );

    let r_seq = Seq::<FpVesta>::from_vec(vec![
        FpVesta::default(),
        FpVesta::default(),
        FpVesta::default(),
    ]);
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| FpVesta::from_literal((*e)))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let n_g = p1.len() / n + 1;
    let poly_parts = step_5(p1, n, n_g);
    let commitments = step_6(poly_parts, &crs, r_seq);
}

#[cfg(test)]
#[quickcheck]
fn test_vanishing_poly(omega_value: usize, n: usize) {
    let omega: FpVesta = FpVesta::from_literal((omega_value as u128 % 50) + 1);
    let n = n % 20 + 2;

    let vanishing_poly = compute_vanishing_polynomial(omega, n);
    for i in 0..(n) {
        let should_be_zero = eval_polyx(vanishing_poly.clone(), omega.pow(i as u128));
        assert_eq!(should_be_zero, FpVesta::ZERO())
    }
    let vanishing_degree: usize = degree_polyx(vanishing_poly);
    assert_eq!(vanishing_degree, n);
}

//Unit test of rotate_polyx from Halo2
#[cfg(test)]
#[quickcheck]
fn test_rotate(
    x: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
    a6: usize,
) {
    let omega =
        FpVesta::from_hex("3a57bee9fb370430aa5f610ed09c17fe7e538bca7c94ad2b1ba3a33bc04980a4"); //omega from halo2
    let x = FpVesta::from_literal(x as u128);
    let a0 = FpVesta::from_literal(a0 as u128);
    let a1 = FpVesta::from_literal(a1 as u128);
    let a2 = FpVesta::from_literal(a2 as u128);
    let a3 = FpVesta::from_literal(a3 as u128);
    let a4 = FpVesta::from_literal(a4 as u128);
    let a5 = FpVesta::from_literal(a5 as u128);
    let a6 = FpVesta::from_literal(a6 as u128);
    let a7 = a0 * a1 * a2 + a5; //pseudo random as quickheck only allows 8 arguments

    let poly = Seq::<FpVesta>::from_vec(vec![a0, a1, a2, a3, a4, a5, a6, a7]);
    assert_eq!(poly.len(), 8);

    let poly_rotated_cur = rotate_polyx(poly.clone(), FpVesta::ONE());
    let poly_rotated_next = rotate_polyx(poly.clone(), omega);
    let poly_rotated_prev = rotate_polyx(poly.clone(), omega.inv());

    assert_eq!(
        eval_polyx(poly.clone(), x),
        eval_polyx(poly_rotated_cur.clone(), x),
    );
    assert_eq!(
        eval_polyx(poly.clone(), x * omega),
        eval_polyx(poly_rotated_next.clone(), x),
    );
    assert_eq!(
        eval_polyx(poly.clone(), x * omega.inv()),
        eval_polyx(poly_rotated_prev.clone(), x),
    );
}

#[cfg(test)]
#[test]
fn automatic_negative_illegal_circut_example_run() {
    fn a(
        a0_0: usize,
        a0_1: usize,
        a0_2: usize,
        a0_3: usize,
        a1_0: usize,
        a1_2: usize,
        a2_0: usize,
        a2_2: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a0_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(a0_1 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a0_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(a0_3 as u128)),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a1_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a1_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a2_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a2_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add.clone());

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(3 as u128),
            FpVesta::from_literal(4523 as u128),
            FpVesta::from_literal(838 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
        let fat_a_1: &Seq<FpVesta> = &fat_a[1];
        let fat_a_2: &Seq<FpVesta> = &fat_a[2];
        // recreate g'(x) from **a**
        let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
            * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()]
                - fat_a_0[1]);

        let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
            n,
            omega,
            x_challenge,
            x1_challenge,
            r,
            s_is,
            q.clone(),
            sigma_list.clone(),
            g_prime_eval_combined_from_a,
            g_prime,
        );

        let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
        let (Q_prime, q_prime, Q_prime_blind) = step_14(
            &crs,
            x2_challenge,
            q_is.clone(),
            r_is_prover,
            q.clone(),
            step14_blinding,
            omega,
            x_challenge,
        );

        let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

        let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

        let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

        let (P, v) = step_18(
            x_challenge,
            x1_challenge,
            x2_challenge,
            x3_challenge,
            x4_challenge,
            omega,
            Q_prime,
            Q_is,
            u.clone(),
            r_is_verifier,
            q,
        );

        let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

        let step20_blinding: FpVesta = FpVesta::from_literal(532 as u128);
        let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
            (
                FpVesta::from_literal(729 as u128),
                FpVesta::from_literal(23 as u128),
            ),
            (
                FpVesta::from_literal(73 as u128),
                FpVesta::from_literal(102 as u128),
            ),
            (
                FpVesta::from_literal(444 as u128),
                FpVesta::from_literal(484 as u128),
            ),
            (x3_challenge, FpVesta::ZERO()),
        ]);
        let s_poly: Polyx = lagrange_polyx(s_poly_points);

        let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

        let (xi, z) = step_21(
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        );

        let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

        let (p_prime_poly, p_prime_blind) =
            step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

        let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(549 as u128),
            FpVesta::from_literal(634 as u128),
        ]);
        let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(827 as u128),
            FpVesta::from_literal(826 as u128),
        ]);
        let u_challenges: Polyx = Seq::from_vec(vec![
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        ]);
        let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
            p_prime_poly,
            G,
            x3_challenge,
            z,
            U,
            W,
            n,
            2,
            u_challenges.clone(),
            L_blinding,
            R_blinding,
        );
        let (c, f) = step_25(
            p_prime,
            L_blinding,
            R_blinding,
            p_prime_blind,
            u_challenges.clone(),
        );

        let V_accepts = step_26(
            u_challenges,
            L,
            P_prime,
            R,
            c,
            G_prime[usize::zero()],
            b[usize::zero()],
            z,
            U,
            f,
            W,
        );

        assert!(!V_accepts);
        TestResult::passed()
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            a0_0: usize,
            a0_1: usize,
            a0_2: usize,
            a0_3: usize,
            a1_0: usize,
            a1_2: usize,
            a2_0: usize,
            a2_2: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn automatic_positive_legal_blinding_example_run() {
    fn a(
        rnd1: usize,
        rnd2: usize,
        rnd3: usize,
        rnd4: usize,
        rnd5: usize,
        rnd6: usize,
        rnd7: usize,
        rnd8: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(rnd1 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(2 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(10 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(5 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(26 as u128)),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(3 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(8 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(5 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(13 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(rnd2 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(rnd3 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(rnd4 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add.clone());

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(rnd5 as u128),
            FpVesta::from_literal(rnd6 as u128),
            FpVesta::from_literal(rnd7 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
        let fat_a_1: &Seq<FpVesta> = &fat_a[1];
        let fat_a_2: &Seq<FpVesta> = &fat_a[2];
        // recreate g'(x) from **a**
        let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
            * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()]
                - fat_a_0[1]);

        let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
            n,
            omega,
            x_challenge,
            x1_challenge,
            r,
            s_is,
            q.clone(),
            sigma_list.clone(),
            g_prime_eval_combined_from_a,
            g_prime,
        );

        let step14_blinding: FpVesta = FpVesta::from_literal(rnd8 as u128);
        let (Q_prime, q_prime, Q_prime_blind) = step_14(
            &crs,
            x2_challenge,
            q_is.clone(),
            r_is_prover,
            q.clone(),
            step14_blinding,
            omega,
            x_challenge,
        );

        let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

        let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

        let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

        let (P, v) = step_18(
            x_challenge,
            x1_challenge,
            x2_challenge,
            x3_challenge,
            x4_challenge,
            omega,
            Q_prime,
            Q_is,
            u.clone(),
            r_is_verifier,
            q,
        );

        let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

        let step20_blinding: FpVesta =
            FpVesta::from_literal(rnd1 as u128) * FpVesta::from_literal(rnd2 as u128);
        let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
            (
                FpVesta::from_literal(729 as u128),
                FpVesta::from_literal(23 as u128),
            ),
            (
                FpVesta::from_literal(73 as u128),
                FpVesta::from_literal(102 as u128),
            ),
            (
                FpVesta::from_literal(444 as u128),
                FpVesta::from_literal(484 as u128),
            ),
            (x3_challenge, FpVesta::ZERO()),
        ]);
        let s_poly: Polyx = lagrange_polyx(s_poly_points);

        let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

        let (xi, z) = step_21(
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        );

        let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

        let (p_prime_poly, p_prime_blind) =
            step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

        let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(rnd1 as u128) * FpVesta::from_literal(rnd3 as u128),
            FpVesta::from_literal(rnd1 as u128) * FpVesta::from_literal(rnd4 as u128),
        ]);
        let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(rnd1 as u128) + FpVesta::from_literal(rnd5 as u128),
            FpVesta::from_literal(rnd1 as u128) + FpVesta::from_literal(rnd7 as u128),
        ]);
        let u_challenges: Polyx = Seq::from_vec(vec![
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        ]);
        let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
            p_prime_poly,
            G,
            x3_challenge,
            z,
            U,
            W,
            n,
            2,
            u_challenges.clone(),
            L_blinding,
            R_blinding,
        );
        let (c, f) = step_25(
            p_prime,
            L_blinding,
            R_blinding,
            p_prime_blind,
            u_challenges.clone(),
        );

        let V_accepts = step_26(
            u_challenges,
            L,
            P_prime,
            R,
            c,
            G_prime[usize::zero()],
            b[usize::zero()],
            z,
            U,
            f,
            W,
        );

        assert!(V_accepts);
        TestResult::passed()
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            rnd1: usize,
            rnd2: usize,
            rnd3: usize,
            rnd4: usize,
            rnd5: usize,
            rnd6: usize,
            rnd7: usize,
            rnd8: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn automatic_positive_legal_challenges_example_run() {
    fn a(
        rnd1: usize,
        rnd2: usize,
        rnd3: usize,
        rnd4: usize,
        rnd5: usize,
        rnd6: usize,
        rnd7: usize,
        rnd8: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let mut rnd1 = rnd1;
        if rnd1 < 2 {
            rnd1 = 2;
        }
        let mut rnd2 = rnd2;
        if rnd2 < 2 {
            rnd2 = 2;
        }
        let mut rnd3 = rnd3;
        if rnd3 < 2 {
            rnd3 = 3;
        }
        let mut rnd4 = rnd4;
        if rnd4 < 2 {
            rnd4 = 2;
        }
        let mut rnd5 = rnd5;
        if rnd5 < 2 {
            rnd5 = 2;
        }
        let mut rnd6 = rnd6;
        if rnd6 < 2 {
            rnd6 = 2;
        }
        let mut rnd7 = rnd7;
        if rnd7 < 2 {
            rnd7 = 2;
        }
        let mut rnd8 = rnd8;
        if rnd8 < 2 {
            rnd8 = 2;
        }
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(124 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(2 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(10 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(5 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(26 as u128)),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(3 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(8 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(5 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(13 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(83838 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(423 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(2308982 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add.clone());

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(23488 as u128),
            FpVesta::from_literal(2389488 as u128),
            FpVesta::from_literal(23 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(rnd1 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(rnd2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(rnd3 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
        let fat_a_1: &Seq<FpVesta> = &fat_a[1];
        let fat_a_2: &Seq<FpVesta> = &fat_a[2];
        // recreate g'(x) from **a**
        let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
            * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()]
                - fat_a_0[1]);

        let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
            n,
            omega,
            x_challenge,
            x1_challenge,
            r,
            s_is,
            q.clone(),
            sigma_list.clone(),
            g_prime_eval_combined_from_a,
            g_prime,
        );

        let step14_blinding: FpVesta = FpVesta::from_literal(918238 as u128);
        let (Q_prime, q_prime, Q_prime_blind) = step_14(
            &crs,
            x2_challenge,
            q_is.clone(),
            r_is_prover,
            q.clone(),
            step14_blinding,
            omega,
            x_challenge,
        );

        let x3_challenge: FpVesta = step_15(FpVesta::from_literal(rnd4 as u128));

        let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

        let x4_challenge: FpVesta = step_17(FpVesta::from_literal(rnd5 as u128));

        let (P, v) = step_18(
            x_challenge,
            x1_challenge,
            x2_challenge,
            x3_challenge,
            x4_challenge,
            omega,
            Q_prime,
            Q_is,
            u.clone(),
            r_is_verifier,
            q,
        );

        let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

        let step20_blinding: FpVesta = FpVesta::from_literal(2348888 as u128);
        let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
            (
                FpVesta::from_literal(729 as u128),
                FpVesta::from_literal(23 as u128),
            ),
            (
                FpVesta::from_literal(73 as u128),
                FpVesta::from_literal(102 as u128),
            ),
            (
                FpVesta::from_literal(444 as u128),
                FpVesta::from_literal(484 as u128),
            ),
            (x3_challenge, FpVesta::ZERO()),
        ]);
        let s_poly: Polyx = lagrange_polyx(s_poly_points);

        let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

        let (xi, z) = step_21(
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        );

        let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

        let (p_prime_poly, p_prime_blind) =
            step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

        let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(999999 as u128),
            FpVesta::from_literal(726 as u128),
        ]);
        let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(3488483 as u128),
            FpVesta::from_literal(39291929 as u128),
        ]);
        let u_challenges: Polyx = Seq::from_vec(vec![
            FpVesta::from_literal(rnd6 as u128),
            FpVesta::from_literal(rnd7 as u128),
        ]);
        let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
            p_prime_poly,
            G,
            x3_challenge,
            z,
            U,
            W,
            n,
            2,
            u_challenges.clone(),
            L_blinding,
            R_blinding,
        );
        let (c, f) = step_25(
            p_prime,
            L_blinding,
            R_blinding,
            p_prime_blind,
            u_challenges.clone(),
        );

        let V_accepts = step_26(
            u_challenges,
            L,
            P_prime,
            R,
            c,
            G_prime[usize::zero()],
            b[usize::zero()],
            z,
            U,
            f,
            W,
        );

        assert!(V_accepts);
        TestResult::passed()
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            rnd1: usize,
            rnd2: usize,
            rnd3: usize,
            rnd4: usize,
            rnd5: usize,
            rnd6: usize,
            rnd7: usize,
            rnd8: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn automatic_positive_legal_circut_example_run() {
    fn a(
        a0_0: usize,
        a0_2: usize,
        a1_0: usize,
        a1_2: usize,
        a2_0: usize,
        a2_2: usize,
    ) -> TestResult {
        /*
         * let n = 2^2 = 4
         * then ω = big is 4 prime root of unity over Fp::Canvas
         *
         * | i | a_0 | a_1 | a_2 | q_add |
         * |---|-----|-----|-----|-------|
         * | 0 | 2   | 3   | 5   | 1     |
         * | 1 | 10  |     |     | 0     |
         * | 2 | 5   | 8   | 13  | 1     |
         * | 3 | 26  |     |     | 0     |
         *
         * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
         * and g(ω^i) = 0 for all i in [0,n) (should hold)
         *
         *
         */
        let n: usize = 4;
        let n_a: usize = 3;
        let n_q: usize = 2;
        let n_g = 4;
        let omega: FpVesta =
            FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
        let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
            g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
            g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
        ]);
        let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
        let crs: CRS = (G.clone(), W);
        let U: G1_pallas =
            g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

        let r_poly = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(13 as u128),
            FpVesta::from_literal(1123 as u128),
            FpVesta::from_literal(1444 as u128),
            FpVesta::from_literal(9991 as u128),
        ]);
        let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
        let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

        let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::<usize>::from_vec(vec![0, 1]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
            Seq::<usize>::from_vec(vec![usize::zero()]),
        ]);

        let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a0_0 as u128)),
            (
                omega.pow(1 as u128),
                FpVesta::from_literal(a0_0 as u128)
                    + FpVesta::from_literal(a1_0 as u128)
                    + FpVesta::from_literal(a2_0 as u128),
            ),
            (omega.pow(2 as u128), FpVesta::from_literal(a0_2 as u128)),
            (
                omega.pow(3 as u128),
                FpVesta::from_literal(a0_2 as u128)
                    + FpVesta::from_literal(a1_2 as u128)
                    + FpVesta::from_literal(a2_2 as u128),
            ),
        ]);

        let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a1_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a1_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(a2_0 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(a2_2 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
            (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
            (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
            (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
        ]);

        let a_0: Polyx = lagrange_polyx(a0_points);
        let a_1: Polyx = lagrange_polyx(a1_points);
        let a_2: Polyx = lagrange_polyx(a2_points);
        let a_primes: Seq<Polyx> =
            Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
        let q_add: Polyx = lagrange_polyx(q_add_points);

        // construct A_i's (commitments)
        let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
        let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
        let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
        let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
        let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
        let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
        let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
        // save a_blinds
        let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

        // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
        let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
        g_prime = add_polyx(g_prime, a_2.clone());
        let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
        g_prime = sub_polyx(g_prime, a_0_rotated);
        g_prime = mul_polyx(g_prime, q_add.clone());

        let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
            Seq::from_vec(vec![usize::zero()]),
            Seq::from_vec(vec![0, 1]),
        ]);
        let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

        let h: Polyx = step_4(g_prime.clone(), omega, n);

        let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

        let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(3 as u128),
            FpVesta::from_literal(4523 as u128),
            FpVesta::from_literal(838 as u128),
        ]);
        let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

        let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
        let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

        let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

        let (r, fat_a) = step_9(
            r_poly.clone(),
            a_primes.clone(),
            omega,
            p.clone(),
            x_challenge,
        );

        let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

        let x1_challenge = FpVesta::from_literal(2 as u128);
        let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

        let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
            n_a,
            x1_challenge,
            x2_challenge,
            H_prime,
            R,
            A_list,
            q.clone(),
            sigma_list.clone(),
        );

        let (q_is, q_blinds) = step_12(
            n_a,
            x1_challenge,
            h_prime,
            r_poly,
            a_primes.clone(),
            q.clone(),
            sigma_list.clone(),
            a_blinds,
            R_blind,
            h_prime_blind,
        );

        let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
        let fat_a_1: &Seq<FpVesta> = &fat_a[1];
        let fat_a_2: &Seq<FpVesta> = &fat_a[2];
        // recreate g'(x) from **a**
        let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
            * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()]
                - fat_a_0[1]);

        let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
            n,
            omega,
            x_challenge,
            x1_challenge,
            r,
            s_is,
            q.clone(),
            sigma_list.clone(),
            g_prime_eval_combined_from_a,
            g_prime,
        );

        let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
        let (Q_prime, q_prime, Q_prime_blind) = step_14(
            &crs,
            x2_challenge,
            q_is.clone(),
            r_is_prover,
            q.clone(),
            step14_blinding,
            omega,
            x_challenge,
        );

        let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

        let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

        let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

        let (P, v) = step_18(
            x_challenge,
            x1_challenge,
            x2_challenge,
            x3_challenge,
            x4_challenge,
            omega,
            Q_prime,
            Q_is,
            u.clone(),
            r_is_verifier,
            q,
        );

        let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

        let step20_blinding: FpVesta = FpVesta::from_literal(532 as u128);
        let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
            (
                FpVesta::from_literal(729 as u128),
                FpVesta::from_literal(23 as u128),
            ),
            (
                FpVesta::from_literal(73 as u128),
                FpVesta::from_literal(102 as u128),
            ),
            (
                FpVesta::from_literal(444 as u128),
                FpVesta::from_literal(484 as u128),
            ),
            (x3_challenge, FpVesta::ZERO()),
        ]);
        let s_poly: Polyx = lagrange_polyx(s_poly_points);

        let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

        let (xi, z) = step_21(
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        );

        let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

        let (p_prime_poly, p_prime_blind) =
            step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

        let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(549 as u128),
            FpVesta::from_literal(634 as u128),
        ]);
        let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
            FpVesta::from_literal(827 as u128),
            FpVesta::from_literal(826 as u128),
        ]);
        let u_challenges: Polyx = Seq::from_vec(vec![
            FpVesta::from_literal(2 as u128),
            FpVesta::from_literal(2 as u128),
        ]);
        let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
            p_prime_poly,
            G,
            x3_challenge,
            z,
            U,
            W,
            n,
            2,
            u_challenges.clone(),
            L_blinding,
            R_blinding,
        );
        let (c, f) = step_25(
            p_prime,
            L_blinding,
            R_blinding,
            p_prime_blind,
            u_challenges.clone(),
        );

        let V_accepts = step_26(
            u_challenges,
            L,
            P_prime,
            R,
            c,
            G_prime[usize::zero()],
            b[usize::zero()],
            z,
            U,
            f,
            W,
        );

        assert!(V_accepts);
        TestResult::passed()
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            a0_0: usize,
            a0_2: usize,
            a1_0: usize,
            a1_2: usize,
            a2_0: usize,
            a2_2: usize,
        ) -> TestResult,
    );
}

#[cfg(test)]
#[test]
fn negative_illegal_circut_example_run() {
    /*
     * let n = 2^2 = 4
     * then ω = big is 4 prime root of unity over Fp::Canvas
     *
     * | i | a_0 | a_1 | a_2 | q_add |
     * |---|-----|-----|-----|-------|
     * | 0 | 2   | 3   | 5   | 1     |
     * | 1 | 10  |     |     | 0     |
     * | 2 | 5   | 8   | 13  | 1     |
     * | 3 | 26  |     |     | 0     |
     *
     * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
     * and g(ω^i) = 0 for all i in [0,n) (should hold)
     *
     *
     */
    let n: usize = 4;
    let n_a: usize = 3;
    let n_q: usize = 2;
    let n_g = 4;
    let omega: FpVesta =
        FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
    let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
        g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
    ]);
    let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
    let crs: CRS = (G.clone(), W);
    let U: G1_pallas = g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

    let r_poly = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(13 as u128),
        FpVesta::from_literal(1123 as u128),
        FpVesta::from_literal(1444 as u128),
        FpVesta::from_literal(9991 as u128),
    ]);
    let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
    let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

    let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
        Seq::<usize>::from_vec(vec![0, 1]),
        Seq::<usize>::from_vec(vec![usize::zero()]),
        Seq::<usize>::from_vec(vec![usize::zero()]),
    ]);

    let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(2 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(10 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(5 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(27 as u128)),
    ]);

    let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(3 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(8 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
    ]);

    let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(5 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(13 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
    ]);

    let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
    ]);

    let a_0: Polyx = lagrange_polyx(a0_points);
    let a_1: Polyx = lagrange_polyx(a1_points);
    let a_2: Polyx = lagrange_polyx(a2_points);
    let a_primes: Seq<Polyx> = Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
    let q_add: Polyx = lagrange_polyx(q_add_points);

    // construct A_i's (commitments)
    let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
    let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
    let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
    let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
    let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
    let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
    let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
    // save a_blinds
    let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

    // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
    let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
    g_prime = add_polyx(g_prime, a_2.clone());
    let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
    g_prime = sub_polyx(g_prime, a_0_rotated);
    g_prime = mul_polyx(g_prime, q_add.clone());

    let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
        Seq::from_vec(vec![usize::zero()]),
        Seq::from_vec(vec![0, 1]),
    ]);
    let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

    let h: Polyx = step_4(g_prime.clone(), omega, n);

    let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

    let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(3 as u128),
        FpVesta::from_literal(4523 as u128),
        FpVesta::from_literal(838 as u128),
    ]);
    let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

    let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
    let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

    let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

    let (r, fat_a) = step_9(
        r_poly.clone(),
        a_primes.clone(),
        omega,
        p.clone(),
        x_challenge,
    );

    let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

    let x1_challenge = FpVesta::from_literal(2 as u128);
    let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

    let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
        n_a,
        x1_challenge,
        x2_challenge,
        H_prime,
        R,
        A_list,
        q.clone(),
        sigma_list.clone(),
    );

    let (q_is, q_blinds) = step_12(
        n_a,
        x1_challenge,
        h_prime,
        r_poly,
        a_primes.clone(),
        q.clone(),
        sigma_list.clone(),
        a_blinds,
        R_blind,
        h_prime_blind,
    );

    let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
    let fat_a_1: &Seq<FpVesta> = &fat_a[1];
    let fat_a_2: &Seq<FpVesta> = &fat_a[2];
    // recreate g'(x) from **a**
    let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
        * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()] - fat_a_0[1]);

    let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
        n,
        omega,
        x_challenge,
        x1_challenge,
        r,
        s_is,
        q.clone(),
        sigma_list.clone(),
        g_prime_eval_combined_from_a,
        g_prime,
    );

    let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
    let (Q_prime, q_prime, Q_prime_blind) = step_14(
        &crs,
        x2_challenge,
        q_is.clone(),
        r_is_prover,
        q.clone(),
        step14_blinding,
        omega,
        x_challenge,
    );

    let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

    let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

    let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

    let (P, v) = step_18(
        x_challenge,
        x1_challenge,
        x2_challenge,
        x3_challenge,
        x4_challenge,
        omega,
        Q_prime,
        Q_is,
        u.clone(),
        r_is_verifier,
        q,
    );

    let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

    let step20_blinding: FpVesta = FpVesta::from_literal(532 as u128);
    let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
        (
            FpVesta::from_literal(729 as u128),
            FpVesta::from_literal(23 as u128),
        ),
        (
            FpVesta::from_literal(73 as u128),
            FpVesta::from_literal(102 as u128),
        ),
        (
            FpVesta::from_literal(444 as u128),
            FpVesta::from_literal(484 as u128),
        ),
        (x3_challenge, FpVesta::ZERO()),
    ]);
    let s_poly: Polyx = lagrange_polyx(s_poly_points);

    let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

    let (xi, z) = step_21(
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(2 as u128),
    );

    let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

    let (p_prime_poly, p_prime_blind) = step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

    let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(549 as u128),
        FpVesta::from_literal(634 as u128),
    ]);
    let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(827 as u128),
        FpVesta::from_literal(826 as u128),
    ]);
    let u_challenges: Polyx = Seq::from_vec(vec![
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(2 as u128),
    ]);
    let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
        p_prime_poly,
        G,
        x3_challenge,
        z,
        U,
        W,
        n,
        2,
        u_challenges.clone(),
        L_blinding,
        R_blinding,
    );
    let (c, f) = step_25(
        p_prime,
        L_blinding,
        R_blinding,
        p_prime_blind,
        u_challenges.clone(),
    );

    let V_accepts = step_26(
        u_challenges,
        L,
        P_prime,
        R,
        c,
        G_prime[usize::zero()],
        b[usize::zero()],
        z,
        U,
        f,
        W,
    );

    assert!(!V_accepts);
}
#[cfg(test)]
#[test]
fn example_run() {
    /*
     * let n = 2^2 = 4
     * then ω = big is 4 prime root of unity over Fp::Canvas
     *
     * | i | a_0 | a_1 | a_2 | q_add |
     * |---|-----|-----|-----|-------|
     * | 0 | 2   | 3   | 5   | 1     |
     * | 1 | 10  |     |     | 0     |
     * | 2 | 5   | 8   | 13  | 1     |
     * | 3 | 26  |     |     | 0     |
     *
     * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
     * and g(ω^i) = 0 for all i in [0,n) (should hold)
     *
     *
     */
    let n: usize = 4;
    let n_a: usize = 3;
    let n_q: usize = 2;
    let n_g = 4;
    let omega: FpVesta =
        FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
    let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
        g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
    ]);
    let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
    let crs: CRS = (G.clone(), W);
    let U: G1_pallas = g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

    let r_poly = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(13 as u128),
        FpVesta::from_literal(1123 as u128),
        FpVesta::from_literal(1444 as u128),
        FpVesta::from_literal(9991 as u128),
    ]);
    let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
    let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

    let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
        Seq::<usize>::from_vec(vec![0, 1]),
        Seq::<usize>::from_vec(vec![usize::zero()]),
        Seq::<usize>::from_vec(vec![usize::zero()]),
    ]);

    let a0_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(2 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(10 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(5 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(26 as u128)),
    ]);

    let a1_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(3 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(8 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
    ]);

    let a2_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(5 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(13 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
    ]);

    let q_add_points: Seq<(FpVesta, FpVesta)> = Seq::<(FpVesta, FpVesta)>::from_vec(vec![
        (omega.pow(0 as u128), FpVesta::from_literal(1 as u128)),
        (omega.pow(1 as u128), FpVesta::from_literal(0 as u128)),
        (omega.pow(2 as u128), FpVesta::from_literal(1 as u128)),
        (omega.pow(3 as u128), FpVesta::from_literal(0 as u128)),
    ]);

    let a_0: Polyx = lagrange_polyx(a0_points);
    let a_1: Polyx = lagrange_polyx(a1_points);
    let a_2: Polyx = lagrange_polyx(a2_points);
    let a_primes: Seq<Polyx> = Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);
    let q_add: Polyx = lagrange_polyx(q_add_points);

    // construct A_i's (commitments)
    let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
    let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
    let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
    let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
    let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
    let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
    let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
    // save a_blinds
    let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

    // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
    let mut g_prime: Polyx = add_polyx(a_0.clone(), a_1.clone());
    g_prime = add_polyx(g_prime, a_2.clone());
    let a_0_rotated: Polyx = rotate_polyx(a_0.clone(), omega);
    g_prime = sub_polyx(g_prime, a_0_rotated);
    g_prime = mul_polyx(g_prime, q_add.clone());
    for i in 0..4 {
        assert_eq!(
            eval_polyx(g_prime.clone(), omega.pow(i as u128)),
            FpVesta::ZERO()
        );
    }

    let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
        Seq::from_vec(vec![usize::zero()]),
        Seq::from_vec(vec![0, 1]),
    ]);
    let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

    let h: Polyx = step_4(g_prime.clone(), omega, n);

    let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

    let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(3 as u128),
        FpVesta::from_literal(4523 as u128),
        FpVesta::from_literal(838 as u128),
    ]);
    let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

    let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
    let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

    let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

    let (r, fat_a) = step_9(
        r_poly.clone(),
        a_primes.clone(),
        omega,
        p.clone(),
        x_challenge,
    );

    let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

    let x1_challenge = FpVesta::from_literal(2 as u128);
    let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

    let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
        n_a,
        x1_challenge,
        x2_challenge,
        H_prime,
        R,
        A_list,
        q.clone(),
        sigma_list.clone(),
    );

    let (q_is, q_blinds) = step_12(
        n_a,
        x1_challenge,
        h_prime,
        r_poly,
        a_primes.clone(),
        q.clone(),
        sigma_list.clone(),
        a_blinds,
        R_blind,
        h_prime_blind,
    );

    let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
    let fat_a_1: &Seq<FpVesta> = &fat_a[1];
    let fat_a_2: &Seq<FpVesta> = &fat_a[2];
    // recreate g'(x) from **a**
    let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
        * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()] - fat_a_0[1]);

    let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
        n,
        omega,
        x_challenge,
        x1_challenge,
        r,
        s_is,
        q.clone(),
        sigma_list.clone(),
        g_prime_eval_combined_from_a,
        g_prime,
    );

    let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
    let (Q_prime, q_prime, Q_prime_blind) = step_14(
        &crs,
        x2_challenge,
        q_is.clone(),
        r_is_prover,
        q.clone(),
        step14_blinding,
        omega,
        x_challenge,
    );

    let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

    let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

    let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

    let (P, v) = step_18(
        x_challenge,
        x1_challenge,
        x2_challenge,
        x3_challenge,
        x4_challenge,
        omega,
        Q_prime,
        Q_is,
        u.clone(),
        r_is_verifier,
        q,
    );

    let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

    let step20_blinding: FpVesta = FpVesta::from_literal(532 as u128);
    let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
        (
            FpVesta::from_literal(729 as u128),
            FpVesta::from_literal(23 as u128),
        ),
        (
            FpVesta::from_literal(73 as u128),
            FpVesta::from_literal(102 as u128),
        ),
        (
            FpVesta::from_literal(444 as u128),
            FpVesta::from_literal(484 as u128),
        ),
        (x3_challenge, FpVesta::ZERO()),
    ]);
    let s_poly: Polyx = lagrange_polyx(s_poly_points);
    assert_eq!(
        eval_polyx(s_poly.clone(), x3_challenge),
        FpVesta::ZERO(),
        "s(X) should have root at x3"
    );
    assert_eq!(
        degree_polyx(s_poly.clone()),
        n - 1,
        "s(X) should have degree n-1: {}",
        n - 1
    );
    let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

    let (xi, z) = step_21(
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(2 as u128),
    );

    let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

    assert_eq!(
        eval_polyx(p_poly.clone(), x3_challenge),
        v,
        "p(x3) should correspond with v"
    );
    let (p_prime_poly, p_prime_blind) = step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

    let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(549 as u128),
        FpVesta::from_literal(634 as u128),
    ]);
    let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(827 as u128),
        FpVesta::from_literal(826 as u128),
    ]);
    let u_challenges: Polyx = Seq::from_vec(vec![
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(2 as u128),
    ]);
    let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
        p_prime_poly,
        G,
        x3_challenge,
        z,
        U,
        W,
        n,
        2,
        u_challenges.clone(),
        L_blinding,
        R_blinding,
    );
    let (c, f) = step_25(
        p_prime,
        L_blinding,
        R_blinding,
        p_prime_blind,
        u_challenges.clone(),
    );

    let V_accepts = step_26(
        u_challenges,
        L,
        P_prime,
        R,
        c,
        G_prime[usize::zero()],
        b[usize::zero()],
        z,
        U,
        f,
        W,
    );

    assert!(V_accepts);
}

#[cfg(test)]
#[test]
fn test_primitive_root_of_unity() {
    // https://crypto.stackexchange.com/questions/63614/finding-the-n-th-root-of-unity-in-a-finite-field
    let n = 16;
    let mut x = FpVesta::TWO();
    let mut g: FpVesta = FpVesta::ZERO();
    loop {
        g = x.pow_self(FpVesta::max_val() / FpVesta::from_literal(n as u128));
        if g.pow(n / 2) != FpVesta::ONE() {
            break;
        }
        let r: usize = rand::Rng::gen(&mut rand::thread_rng());
        x = x * FpVesta::from_literal(r as u128);
    }
    println!("{:?}", g);
    for i in 0..n * 2 {
        println!("{:?}", g.pow(i as u128))
    }
}

// HERE STARTS IMPLEMENTATION FOR THE POLYNOMIAL RING OVER THE VESTA FIELD ///

/// A polynomial represented by its coefficient form, such that index i is the i'th term
pub type Polyx = Seq<FpVesta>;

/// Add two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
pub fn add_polyx(p1: Polyx, p2: Polyx) -> Polyx {
    let mut res = Seq::<FpVesta>::create(0);
    let mut short_len = 0;

    if p1.len() > p2.len() {
        res = p1.clone();
        short_len = p2.len();
    } else {
        res = p2.clone();
        short_len = p1.len();
    }

    for i in 0..short_len {
        res[i] = p1[i] + p2[i];
    }

    trim_polyx(res)
}

/// Subtract two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
pub fn sub_polyx(p1: Polyx, p2: Polyx) -> Polyx {
    let mut largest = p1.len();
    if p2.len() > p1.len() {
        largest = p2.len();
    }

    let mut res = Seq::<FpVesta>::create(largest);
    for i in 0..p1.len() {
        res[i] = p1[i];
    }

    for i in 0..p2.len() {
        res[i] = res[i] - p2[i];
    }

    trim_polyx(res)
}

/// Polynomial multiplication using sparse multiplication.
/// This can be more efficient than operand scanning but also prone to side-channel
/// attacks.
/// Mostly copied from hacspec's poly_mul
///
/// # Arguments
///
/// * `p1` LHS polynomial
/// * `p2` RHS polynomial
pub fn mul_polyx(a: Polyx, b: Polyx) -> Polyx {
    let mut result = Seq::<FpVesta>::create(a.len() + b.len());
    for i in 0..a.len() {
        if !a[i].equal(FpVesta::default()) {
            for j in 0..b.len() {
                if !b[j].equal(FpVesta::default()) {
                    result[i + j] = (result[i + j].add(a[i] * b[j]));
                }
            }
        }
    }
    trim_polyx(result)
}

/// Multiply a polynomial by a scalar, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
pub fn mul_scalar_polyx(p: Polyx, s: FpVesta) -> Polyx {
    let mut res = p.clone();

    for i in 0..res.len() {
        res[i] = p[i] * s;
    }

    res
}

/// Add a scalar (constant) from a polynomial, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
pub fn add_scalar_polyx(p: Polyx, s: FpVesta) -> Polyx {
    let mut res = p.clone();
    if res.len() == 0 {
        // if poly empty, initialize res to zero constant term
        res = Seq::<FpVesta>::create(1);
    }

    // do the addition on constant term
    res[usize::zero()] = res[usize::zero()] + s;

    res
}

/// Subtract a scalar (constant) from a polynomial, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
pub fn sub_scalar_polyx(p: Polyx, s: FpVesta) -> Polyx {
    let mut res = p.clone();
    if res.len() == 0 {
        // if poly empty, initialize res to zero constant term
        res = Seq::<FpVesta>::create(1);
    }

    // do the subtraction on constant term
    res[usize::zero()] = res[usize::zero()] - s;

    res
}

/// Evaluate a polynomial at point, return the evaluation
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `x` - the point
pub fn eval_polyx(p: Polyx, x: FpVesta) -> FpVesta {
    let mut res = FpVesta::ZERO();

    for i in 0..p.len() {
        res = res + p[i] * x.exp(i as u32);
    }

    res
}

/// Get the degree of a polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
pub fn degree_polyx(p: Polyx) -> usize {
    let len = trim_polyx(p).len();
    if len == 0 {
        0
    } else {
        (len - 1)
    }
}

/// Checks if all entries in a polynomial is 0
/// # Arguments
/// * `p` the polynomial to be checked
/// # Returns
/// * `true` if polynomial is NOT all 0
/// * `false`if polynomial IS all 0
pub fn check_not_zero_polyx(p: Polyx) -> bool {
    let mut sum = FpVesta::ZERO();
    let mut all_zero = false;
    for i in 0..p.len() {
        if p[i] > FpVesta::ZERO() {
            all_zero = true;
        }
    }
    all_zero
}

/// Trim a polynomial of trailing zeros (zero-terms) and return it
///
/// # Arguments
///
/// * `p` - the polynomial
pub fn trim_polyx(p: Polyx) -> Polyx {
    let mut last_val_idx = 1;
    for i in 0..p.len() {
        if p[i] != FpVesta::ZERO() {
            last_val_idx = i + 1;
        }
    }
    let mut res = Seq::<FpVesta>::create(last_val_idx);
    if p.len() != 0 {
        for i in 0..res.len() {
            res[i] = p[i];
        }
    }

    if p.len() == 0 {
        res = p;
    }

    res
}

/// divide the leading terms of two polynomials, returning a single term (e.g. 5x^3) represented as a polynomial
/// (helper function for divide_poly)
///
/// # Arguments
///
/// * `n` - the dividend/enumerator polynomial
/// * `d` - the divisor/denominator polynomial
pub fn divide_leading_terms(n: Polyx, d: Polyx) -> Polyx {
    let n: Polyx = trim_polyx(n);
    let d: Polyx = trim_polyx(d);
    let x_pow: usize = n.len() - d.len();
    let n_coeff: FpVesta = n[n.len() - 1];
    let d_coeff: FpVesta = d[d.len() - 1];
    let coeff: FpVesta = n_coeff / d_coeff;
    let mut res: Polyx = Seq::<FpVesta>::create(x_pow + 1);
    res[x_pow] = coeff;

    res
}

/// Perform polynomial long division, returning the quotient and the remainder.
/// The algorithm is from <https://en.wikipedia.org/wiki/Polynomial_long_division>.
///
/// The pseudo-code is shown here:
///
/// ```text
/// function n / d is
///  require d ≠ 0
///  q ← 0
///  r ← n             // At each step n = d × q + r
///
///  while r ≠ 0 and degree(r) ≥ degree(d) do
///      t ← lead(r) / lead(d)       // Divide the leading terms
///      q ← q + t
///      r ← r − t × d
///
///  return (q, r)
/// ```
///
/// # Arguments
///
/// * `n` - the dividend/enumerator polynomial
/// * `d` - the divisor/denominator polynomial
pub fn divide_polyx(n: Polyx, d: Polyx) -> (Polyx, Polyx) {
    let mut q: Polyx = Seq::<FpVesta>::create(n.len());
    let mut r: Polyx = n.clone();

    let mut loop_upper_bound = d.len();
    if q.len() > d.len() {
        loop_upper_bound = q.len();
    }
    for _ in 0..loop_upper_bound {
        if check_not_zero_polyx(r.clone()) && degree_polyx(r.clone()) >= degree_polyx(d.clone()) {
            let t: Polyx = divide_leading_terms(r.clone(), d.clone());

            q = add_polyx(q, t.clone());
            let aux_prod: Polyx = mul_polyx(d.clone(), t.clone());
            r = sub_polyx(r, aux_prod);
        }
    }

    (trim_polyx(q), trim_polyx(r))
}

/// Wrapper function for multiplying a polynomial with the indeterminate
/// # Arguments
/// * `p` - The polynomial to be multiplied with the indeterminate
pub fn multi_poly_with_x(p: Polyx) -> Polyx {
    multi_poly_with_x_pow(p, 1)
}

/// Wrapper function for multiplying a polynomial with the indeterminate multiple times
/// # Arguments
/// * `p` - the polynomial to be multiplied with the inderterminate
/// * `power` - the number of times the indeterminate should be multiplied to the polynomial
pub fn multi_poly_with_x_pow(p: Polyx, power: usize) -> Polyx {
    let p: Polyx = trim_polyx(p);
    let mut res: Polyx = Seq::<FpVesta>::create(p.len() + power);

    for i in 0..p.len() {
        res[i + power] = p[i];
    }
    res
}

///Find lowest degree polynomial passing through a set points using legrange interpolation
/// # Arguments
/// * `points`is a sequence of points `(Fp,Fp)` that the polynomial must pass through
/// # Assertions
/// * No two points may have the same x-value.
pub fn lagrange_polyx(points: Seq<(FpVesta, FpVesta)>) -> Polyx {
    let mut poly = Seq::<FpVesta>::create(points.len());

    for i in 0..points.len() {
        let x: FpVesta = points[i].0;
        let y: FpVesta = points[i].1;
        let basis = lagrange_basis(points.clone(), x);
        let scaled_basis = mul_scalar_polyx(basis, y);
        poly = add_polyx(poly.clone(), scaled_basis.clone());
    }
    poly = trim_polyx(poly);
    poly
}

/// Finds the Lagrange basis for a set of `points` and a single evaluation point `x`
/// This will produce a polynomial that evaluates to 1 at `x`and to 0 at all other x-values in the set `points`
/// No other guarentees are given about the resulting polynomial
///
/// # Arguments
/// * `points`is a sequence of points `(Fp,Fp)` whose x-values the polynomial wil evaluate to 0 at
/// * `x`is the x-value where the polynomial will evaluate to 1. If `x`is also in `points` the polynomial will still evaluate to 1 at `x``
/// # Assertions
/// * No two points may have the same x-value
pub fn lagrange_basis(points: Seq<(FpVesta, FpVesta)>, x: FpVesta) -> Polyx {
    let mut basis = Seq::<FpVesta>::create(points.len());
    basis[usize::zero()] = FpVesta::ONE();
    let mut devisor = FpVesta::ONE();
    for i in 0..points.len() {
        let point = points[i];
        let p_x = point.0;
        if p_x != x {
            devisor = devisor.mul(x.sub(p_x));
            let poly_mul_x = multi_poly_with_x(basis.clone());
            let poly_mul_scalar: Polyx = mul_scalar_polyx(basis.clone(), p_x.neg());
            basis = add_polyx(poly_mul_x, poly_mul_scalar);
        }
    }
    let test = eval_polyx(basis.clone(), FpVesta::ONE());
    let mut division_poly = Seq::<FpVesta>::create(points.len());
    division_poly[usize::zero()] = devisor;

    let output = divide_polyx(basis.clone(), division_poly.clone());

    let (final_basis, _) = output;

    final_basis
}

// functions used for testing of polyx

fn gen_zero_polyx() -> Polyx {
    let poly = Seq::<FpVesta>::create(1);
    poly
}

fn gen_one_polyx() -> Polyx {
    let mut poly = Seq::<FpVesta>::create(1);
    poly[usize::zero()] = FpVesta::ONE();
    poly
}

fn check_equal_polyx(p1: Polyx, p2: Polyx) -> bool {
    let mut is_equal = false;
    if trim_polyx(p1.clone()).len() == trim_polyx(p2.clone()).len() {
        is_equal = true;
        for i in 0..trim_polyx(p1.clone()).len() {
            let p1_scaler_i = p1[i].clone();
            let p2_scaler_i = p2[i].clone();
            if p1_scaler_i != p2_scaler_i {
                is_equal = false;
            }
        }
    }
    is_equal
}

#[cfg(test)]
#[derive(Clone, Debug, Default)]
struct PolyxContainer(Polyx);
#[cfg(test)]
impl Arbitrary for PolyxContainer {
    fn arbitrary(g: &mut quickcheck::Gen) -> PolyxContainer {
        let size = u8::arbitrary(g);
        let mut v: Vec<FpVesta> = vec![];
        for _ in 0..size {
            let new_val: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            v.push(new_val);
        }
        PolyxContainer(Seq::<FpVesta>::from_vec(v))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_logic(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x as u128);
    let sum_poly = add_polyx(p1.clone(), p2.clone());

    let expected = eval_polyx(p1, x) + eval_polyx(p2, x);
    let actual = eval_polyx(sum_poly, x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_closure(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = add_polyx(p1.clone(), p2.clone());
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_associativity(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;
    let p4 = add_polyx(p1.clone(), p2.clone());
    let p4 = add_polyx(p4.clone(), p3.clone());
    let p5 = add_polyx(p2.clone(), p3.clone());
    let p5 = add_polyx(p5.clone(), p1.clone());
    assert!(check_equal_polyx(p5, p4))
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_identity(p1: PolyxContainer) {
    let p1 = p1.0;

    let p2 = add_polyx(p1.clone(), gen_zero_polyx());

    let p3 = add_polyx(gen_zero_polyx(), p1.clone());

    assert!(check_equal_polyx(p1, p2.clone()));
    assert!(check_equal_polyx(p3, p2));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_inverse(p1: PolyxContainer) {
    let p1 = p1.0;
    let p1_inv = sub_polyx(gen_zero_polyx(), p1.clone());
    let p3 = add_polyx(p1.clone(), p1_inv.clone());
    let p4 = add_polyx(p1_inv, p1);
    assert!(check_equal_polyx(p3.clone(), p4));
    assert!(check_equal_polyx(p3, gen_zero_polyx()));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_cummutativity(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = add_polyx(p1.clone(), p2.clone());
    let p4 = add_polyx(p2.clone(), p1.clone());
    assert!(check_equal_polyx(p3.clone(), p4));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_right_distributive(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;

    // p4 = p1 * (p2 + p3)
    let p4 = add_polyx(p1.clone(), p2.clone());
    let p4 = mul_polyx(p4.clone(), p3.clone());

    // p5 = (p1 * p2) + (p1 * p3)
    let p5 = mul_polyx(p1.clone(), p3.clone());
    let p6 = mul_polyx(p2.clone(), p3.clone());
    let p5 = add_polyx(p5.clone(), p6.clone());
    assert!(check_equal_polyx(p4, p5));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_logic(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x as u128);
    let mul_poly = mul_polyx(p1.clone(), p2.clone());

    let expected = eval_polyx(p1, x) * eval_polyx(p2, x);
    let actual = eval_polyx(mul_poly, x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_closure(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = mul_polyx(p1.clone(), p2.clone());
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_associativity(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;
    let p4 = mul_polyx(p1.clone(), p2.clone());
    let p4 = mul_polyx(p4.clone(), p3.clone());
    let p5 = mul_polyx(p2.clone(), p3.clone());
    let p5 = mul_polyx(p5.clone(), p1.clone());
    assert!(check_equal_polyx(p5, p4))
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_identity(p1: PolyxContainer) {
    let p1 = p1.0;
    let p2 = mul_polyx(p1.clone(), gen_one_polyx());
    let p3 = mul_polyx(gen_one_polyx(), p1.clone());
    assert!(check_equal_polyx(p1, p2.clone()));
    assert!(check_equal_polyx(p3, p2));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_cummutativity(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = mul_polyx(p1.clone(), p2.clone());
    let p4 = mul_polyx(p2.clone(), p1.clone());
    assert!(check_equal_polyx(p3, p4));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_left_distributive(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;
    // p4 = p1 * (p2 + p3)
    let p4 = add_polyx(p2.clone(), p3.clone());
    let p4 = mul_polyx(p4.clone(), p1.clone());
    // p5 = (p1 * p2) + (p1 * p3)
    let p5 = mul_polyx(p1.clone(), p2.clone());
    let p6 = mul_polyx(p1.clone(), p3.clone());
    let p5 = add_polyx(p5.clone(), p6.clone());
    assert!(check_equal_polyx(p4, p5));
}
///////////////////

#[cfg(test)]
#[quickcheck]
fn test_poly_div(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    if p2.len() > 0 {
        let x = FpVesta::from_literal(x as u128);

        let (q, r) = divide_polyx(p1.clone(), p2.clone());
        let eval_q = eval_polyx(q, x);
        let eval_r = eval_polyx(r, x);
        let eval_r_div = eval_r / eval_polyx(p2.clone(), x);

        let expected = eval_polyx(p1, x) / eval_polyx(p2.clone(), x);
        let actual = eval_q + eval_r_div;

        assert_eq!(expected, actual);
    }
}

#[cfg(test)]
#[quickcheck]
fn test_poly_sub(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x as u128);
    let sum_poly = sub_polyx(p1.clone(), p2.clone());

    let expected = eval_polyx(p1, x) - eval_polyx(p2, x);
    let actual = eval_polyx(sum_poly, x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[test]
fn test_poly_eval() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| FpVesta::from_literal((*e)))
        .collect();
    let p1 = Seq::from_vec(v1);

    assert_eq!(
        eval_polyx(p1, FpVesta::TWO()),
        FpVesta::from_literal(105 as u128)
    );
}

#[cfg(test)]
#[test]
fn test_trim_poly() {
    let p = Seq::from_vec(vec![
        FpVesta::ZERO(),
        FpVesta::from_literal(6 as u128),
        FpVesta::from_literal(4 as u128),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
        FpVesta::from_literal(2 as u128),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
    ]);

    let trimmed_p = trim_polyx(p.clone());
    assert_eq!(trimmed_p.len(), p.len() - 3);
}

#[cfg(test)]
#[quickcheck]
fn test_lagrange(a: Points) {
    let points_seq = a.0;

    let legrange_poly = lagrange_polyx(points_seq.clone());

    for j in 0..points_seq.len() {
        let eval_x = points_seq[j].0;
        let point_y = points_seq[j].1;
        let res = eval_polyx(legrange_poly.clone(), eval_x);
        assert_eq!(res, point_y)
    }
}

#[cfg(test)]
#[quickcheck]
fn test_lagrange_basis(a: Points) {
    let points_seq = a.0;
    for i in 0..points_seq.len() {
        let x = points_seq[i].0;
        let basis = lagrange_basis(points_seq.clone(), x);
        for j in 0..points_seq.len() {
            let eval_x = points_seq[j].0;
            let res = eval_polyx(basis.clone(), eval_x);
            if x == eval_x {
                assert_eq!(res, FpVesta::ONE())
            } else {
                assert_eq!(res, FpVesta::ZERO())
            }
        }
    }
}
