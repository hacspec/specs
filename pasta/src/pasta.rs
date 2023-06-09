#![allow(non_snake_case)]
#![allow(warnings, unused)]

use hacspec_lib::*;

// Pallas: y^2 = x^3 + 5
// Vesta: y^2 = x^3 + 5

// The base field for Pallas and the scalar field for Vesta, from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:
// 28948022309329048855892746252171976963363056481941560715954676764349967630337, or
// 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
public_nat_mod!(
    type_name: FpPallas,
    type_of_canvas: PallasCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC094CF91B992D30ED00000001"
);

// The scalar field for Vesta and the scalar field for Pallas, from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:
// 28948022309329048855892746252171976963363056481941647379679742748393362948097, or
// 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
public_nat_mod!(
    type_name: FpVesta,
    type_of_canvas: VestaCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001"
);

//bool is "isPointAtInfinity"
pub type G1_pallas = (FpPallas, FpPallas, bool);
pub type G1_vesta = (FpVesta, FpVesta, bool);

/* Arithmetic in G1 */

// Create 'default' G1 element (0,0,true)
pub fn g1_default_pallas() -> G1_pallas {
    (FpPallas::ZERO(), FpPallas::ZERO(), true)
}
pub fn g1_default_vesta() -> G1_vesta {
    (FpVesta::ZERO(), FpVesta::ZERO(), true)
}

//g1 add with no Point at Infinity
fn g1add_a_pallas(p: G1_pallas, q: G1_pallas) -> G1_pallas {
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = x2 - x1;
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}
fn g1add_a_vesta(p: G1_vesta, q: G1_vesta) -> G1_vesta {
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = x2 - x1;
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

//g1 double with no Point at Infinity
fn g1double_a_pallas(p: G1_pallas) -> G1_pallas {
    let (x1, y1, _) = p;

    let x12 = x1.exp(2u32);
    let xovery = (FpPallas::from_literal(3u128) * x12) * (FpPallas::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - FpPallas::TWO() * x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}
fn g1double_a_vesta(p: G1_vesta) -> G1_vesta {
    let (x1, y1, _) = p;

    let x12 = x1.exp(2u32);
    let xovery = (FpVesta::from_literal(3u128) * x12) * (FpVesta::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - FpVesta::TWO() * x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

/* Wrapper functions with Point of Infinity */
pub fn g1double_pallas(p: G1_pallas) -> G1_pallas {
    let (_x1, y1, inf1) = p;
    if y1 != FpPallas::ZERO() && !inf1 {
        g1double_a_pallas(p)
    } else {
        (FpPallas::ZERO(), FpPallas::ZERO(), true)
    }
}
pub fn g1double_vesta(p: G1_vesta) -> G1_vesta {
    let (_x1, y1, inf1) = p;
    if y1 != FpVesta::ZERO() && !inf1 {
        g1double_a_vesta(p)
    } else {
        (FpVesta::ZERO(), FpVesta::ZERO(), true)
    }
}

pub fn g1add_pallas(p: G1_pallas, q: G1_pallas) -> G1_pallas {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g1double_pallas(p)
            } else {
                if !(x1 == x2 && y1 == FpPallas::ZERO() - y2) {
                    g1add_a_pallas(p, q)
                } else {
                    (FpPallas::ZERO(), FpPallas::ZERO(), true)
                }
            }
        }
    }
}
pub fn g1add_vesta(p: G1_vesta, q: G1_vesta) -> G1_vesta {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g1double_vesta(p)
            } else {
                if !(x1 == x2 && y1 == FpVesta::ZERO() - y2) {
                    g1add_a_vesta(p, q)
                } else {
                    (FpVesta::ZERO(), FpVesta::ZERO(), true)
                }
            }
        }
    }
}

pub fn g1mul_pallas(m: FpVesta, p: G1_pallas) -> G1_pallas {
    let mut t = (FpPallas::ZERO(), FpPallas::ZERO(), true);
    for i in 0..255 {
        //starting from second most significant bit
        t = g1double_pallas(t);
        if m.bit(254 - i) {
            t = g1add_pallas(t, p);
        }
    }
    t
}
pub fn g1mul_vesta(m: FpPallas, p: G1_vesta) -> G1_vesta {
    let mut t = (FpVesta::ZERO(), FpVesta::ZERO(), true);
    for i in 0..255 {
        //starting from second most significant bit
        t = g1double_vesta(t);
        if m.bit(254 - i) {
            t = g1add_vesta(t, p);
        }
    }
    t
}

pub fn g1neg_pallas(p: G1_pallas) -> G1_pallas {
    let (x, y, inf) = p;
    (x, FpPallas::ZERO() - y, inf)
}

pub fn g1neg_vesta(p: G1_vesta) -> G1_vesta {
    let (x, y, inf) = p;
    (x, FpVesta::ZERO() - y, inf)
}

pub fn g1_on_curve_pallas(p: G1_pallas) -> bool {
    let (x, y, inf) = p;
    let y_squared = y * y;
    let x_cubed = x * x * x;
    let fp5 = FpPallas::TWO() + FpPallas::TWO() + FpPallas::ONE();
    // the point is on the curve IFF
    // the point satisfies y^2 = x^3 + 5
    // or it is the infinity point
    (y_squared == x_cubed + fp5) || inf
}
pub fn g1_on_curve_vesta(p: G1_vesta) -> bool {
    let (x, y, inf) = p;
    let y_squared = y * y;
    let x_cubed = x * x * x;
    let fp5 = FpVesta::TWO() + FpVesta::TWO() + FpVesta::ONE();
    // the point is on the curve IFF
    // the point satisfies y^2 = x^3 + 5
    // or it is the infinity point
    (y_squared == x_cubed + fp5) || inf
}

pub fn g1_is_identity_pallas(p: G1_pallas) -> bool {
    let (_, _, inf) = p;
    inf
}
pub fn g1_is_identity_vesta(p: G1_vesta) -> bool {
    let (_, _, inf) = p;
    inf
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;

// Arbitrary implementation is needed to randomly generate arbitrary elements of the specified type.
// Used in Property based testing to generate random tests

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for FpPallas {
    fn arbitrary(g: &mut Gen) -> FpPallas {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        b[31] = b[31] & 127;
        FpPallas::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for FpVesta {
    fn arbitrary(g: &mut Gen) -> FpVesta {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        b[31] = b[31] & 127;
        FpVesta::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct G1PallasContainer(G1_pallas);

#[cfg(test)]
impl Arbitrary for G1PallasContainer {
    fn arbitrary(g: &mut Gen) -> G1PallasContainer {
        let a = FpVesta::from_literal(u128::arbitrary(g));
        let generator = g1_generator_pallas();
        G1PallasContainer(g1mul_pallas(a, generator))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct G1VestaContainer(G1_vesta);

#[cfg(test)]
impl Arbitrary for G1VestaContainer {
    fn arbitrary(g: &mut Gen) -> G1VestaContainer {
        let a = FpPallas::from_literal(u128::arbitrary(g));
        let generator = g1_generator_vesta();
        G1VestaContainer(g1mul_vesta(a, generator))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_g1_closure_pallas(a: G1PallasContainer, b: G1PallasContainer) {
    let a = a.0;
    let b = b.0;

    let sum = g1add_pallas(a, b);
    assert!(g1_on_curve_pallas(sum));
}
#[cfg(test)]
#[quickcheck]
fn test_g1_closure_vesta(a: G1VestaContainer, b: G1VestaContainer) {
    let a = a.0;
    let b = b.0;

    let sum = g1add_vesta(a, b);
    assert!(g1_on_curve_vesta(sum));
}

#[cfg(test)]
#[quickcheck]
fn test_g1_associativity_pallas(a: G1PallasContainer, b: G1PallasContainer, c: G1PallasContainer) {
    let a = a.0;
    let b = b.0;
    let c = c.0;

    let sum1 = g1add_pallas(g1add_pallas(a, b), c);
    let sum2 = g1add_pallas(a, g1add_pallas(b, c));
    assert_eq!(sum1, sum2);
}
#[cfg(test)]
#[quickcheck]
fn test_g1_associativity_vesta(a: G1VestaContainer, b: G1VestaContainer, c: G1VestaContainer) {
    let a = a.0;
    let b = b.0;
    let c = c.0;

    let sum1 = g1add_vesta(g1add_vesta(a, b), c);
    let sum2 = g1add_vesta(a, g1add_vesta(b, c));
    assert_eq!(sum1, sum2);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_identity_pallas(a: G1PallasContainer) {
    let a = a.0;
    let identity = g1_default_pallas();

    let sum = g1add_pallas(a, identity);

    assert_eq!(sum, a);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_identity_vesta(a: G1VestaContainer) {
    let a = a.0;
    let identity = g1_default_vesta();

    let sum = g1add_vesta(a, identity);

    assert_eq!(sum, a);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_inverse_pallas(a: G1PallasContainer) {
    let a = a.0;
    let a_neg = g1neg_pallas(a);

    let sum = g1add_pallas(a, a_neg);

    assert!(g1_is_identity_pallas(sum));
}
#[cfg(test)]
#[quickcheck]
fn test_g1_inverse_vesta(a: G1VestaContainer) {
    let a = a.0;
    let a_neg = g1neg_vesta(a);

    let sum = g1add_vesta(a, a_neg);

    assert!(g1_is_identity_vesta(sum));
}

#[cfg(test)]
#[test]
fn test_g1_arithmetic_pallas() {
    let g = g1_generator_pallas();

    let g2 = g1double_pallas(g);
    let g4a = g1double_pallas(g2);
    let g3 = g1add_pallas(g2, g);
    let g4b = g1add_pallas(g3, g);
    assert_eq!(g4a, g4b);
}
#[cfg(test)]
#[test]
fn test_g1_arithmetic_vesta() {
    let g = g1_generator_vesta();

    let g2 = g1double_vesta(g);
    let g4a = g1double_vesta(g2);
    let g3 = g1add_vesta(g2, g);
    let g4b = g1add_vesta(g3, g);
    assert_eq!(g4a, g4b);
}

#[cfg(test)]
#[test]
fn test_g1_mul_standard_pallas() {
    let g = g1_generator_pallas();
    let m = FpVesta::ONE();
    assert_eq!(g, g1mul_pallas(m, g));
    let m = FpVesta::from_literal(2u128);
    let g2 = g1double_pallas(g);
    assert_eq!(g2, g1mul_pallas(m, g));
    let m = FpVesta::from_literal(3u128);
    let g3 = g1add_pallas(g, g2);
    assert_eq!(g3, g1mul_pallas(m, g));
}

#[cfg(test)]
#[test]
fn test_g1_mul_standard_vesta() {
    let g = g1_generator_vesta();
    let m = FpPallas::ONE();
    assert_eq!(g, g1mul_vesta(m, g));
    let m = FpPallas::from_literal(2u128);
    let g2 = g1double_vesta(g);
    assert_eq!(g2, g1mul_vesta(m, g));
    let m = FpPallas::from_literal(3u128);
    let g3 = g1add_vesta(g, g2);
    assert_eq!(g3, g1mul_vesta(m, g));
}

#[cfg(test)]
#[test]
fn test_g1_mul_zero_pallas() {
    let g = g1_generator_pallas();
    let m = FpVesta::ZERO();
    let h = g1mul_pallas(m, g);
    assert!(h.2);
}
#[cfg(test)]
#[test]
fn test_g1_mul_zero_vesta() {
    let g = g1_generator_vesta();
    let m = FpPallas::ZERO();
    let h = g1mul_vesta(m, g);
    assert!(h.2);
}

#[cfg(test)]
#[test]
fn test_g1_mul_prop_pallas() {
    fn test_g1_mul_pallas(a: FpVesta) -> bool {
        let g = g1mul_pallas(a, g1_generator_pallas());
        let r = FpVesta::from_hex("0"); //r
        let h = g1mul_pallas(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_pallas as fn(FpVesta) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_mul_prop_vesta() {
    fn test_g1_mul_vesta(a: FpPallas) -> bool {
        let g = g1mul_vesta(a, g1_generator_vesta());
        let r = FpPallas::from_hex("0"); //r
        let h = g1mul_vesta(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_vesta as fn(FpPallas) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv_pallas() {
    fn test_g1_mul_pallas(a: FpVesta) -> bool {
        let g = g1mul_pallas(a, g1_generator_pallas());
        g1add_pallas(g, g) == g1double_pallas(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_pallas as fn(FpVesta) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv_vesta() {
    fn test_g1_mul_vesta(a: FpPallas) -> bool {
        let g = g1mul_vesta(a, g1_generator_vesta());
        g1add_vesta(g, g) == g1double_vesta(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_vesta as fn(FpPallas) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_special_case_pallas() {
    let g = (FpPallas::TWO(), FpPallas::ZERO(), false);
    assert_eq!(g1add_pallas(g, g), g1double_pallas(g));
}

#[cfg(test)]
#[test]
fn test_g1_add_double_special_case_vesta() {
    let g = (FpVesta::TWO(), FpVesta::ZERO(), false);
    assert_eq!(g1add_vesta(g, g), g1double_vesta(g));
}

// Generators taken from:
// https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas
// (mina generator pallas: (1,12418654782883325593414442427049395787963493412651469444558597405572177144507))
#[cfg(test)]
pub fn g1_generator_pallas() -> G1_pallas {
    (
        FpPallas::from_hex("1"),
        FpPallas::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        false,
    )
}

// (mina generator vesta: (1,11426906929455361843568202299992114520848200991084027513389447476559454104162))
#[cfg(test)]
pub fn g1_generator_vesta() -> G1_vesta {
    (
        FpVesta::from_hex("1"),
        FpVesta::from_hex("1943666EA922AE6B13B64E3AAE89754CACCE3A7F298BA20C4E4389B9B0276A62"),
        false,
    )
}
