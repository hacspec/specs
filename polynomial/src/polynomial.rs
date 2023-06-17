#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_lib::*;

pub struct Polynomial<T: Numeric + NumericCopy + Clone> {
    coefficients: Seq<T>,
}

impl<T: Numeric + NumericCopy + PartialEq> Polynomial<T> {
    /// Create a polynomial, defined from its coefficient form
    ///
    /// # Arguments
    ///
    /// * `coefficients` - the polynomial in coefficient form
    pub fn new(coefficients: Seq<T>) -> Polynomial<T> {
        (Polynomial { coefficients }).trim()
    }

    /// Get a clone of the coefficients (useful for printing)
    pub fn coeffs(&self) -> Seq<T> {
        self.coefficients.clone()
    }

    /// Evaluate a polynomial at point, return the evaluation
    ///
    /// # Arguments
    ///
    /// * `x` - the point
    pub fn evaluate(self, x: T) -> T {
        let coefficients = self.coefficients;
        let mut result = T::default();

        for i in 0..coefficients.len() {
            result = result + coefficients[i] * x.exp(i as u32);
        }

        result
    }

    /// Get the polynomial trimmed of trailing zeros
    /// Mostly for internal use
    fn trim(&self) -> Polynomial<T> {
        let len = self.coefficients.len();
        for i in (1..len).rev() {
            if self.coefficients[i] != T::default() {
                return Polynomial {
                    coefficients: self.coefficients.slice(0, i + usize::one()),
                };
            }
        }
        Polynomial {
            coefficients: self.coefficients.slice(0, usize::one()),
        }
    }

    /// Get the degree of the polynomial
    pub fn degree(&self) -> usize {
        self.trim().coefficients.len()
    }

    /// Get the coefficient of the leading term
    pub fn leading_term(&self) -> T {
        let coeffs = self.trim().coefficients;
        coeffs[coeffs.len() - usize::one()]
    }

    /// Get the coefficient of the term at some degree
    ///
    /// # Arguments
    ///
    /// * `degree` - the degree to get coefficient for
    pub fn get_coefficient(&self, degree: usize) -> T {
        if self.trim().coefficients.len() > degree {
            self.coefficients[degree]
        } else {
            T::default()
        }
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Add<Polynomial<T>> for Polynomial<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let lhs = self.coefficients;
        let rhs = other.coefficients;
        let (big, small) = {
            if lhs.len() > rhs.len() {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            }
        };

        let mut result = big.clone();
        for i in 0..small.len() {
            result[i] = result[i].add(small[i]);
        }

        return (Polynomial {
            coefficients: result,
        })
        .trim();
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Add<T> for Polynomial<T> {
    type Output = Self;

    fn add(self, other: T) -> Self {
        let mut c = self.coefficients;
        c[usize::zero()] = c[usize::zero()] + other;
        Polynomial { coefficients: c }
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Sub<Polynomial<T>> for Polynomial<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let rhs = other.coefficients;

        let mut neg_rhs = Seq::<T>::create(rhs.len());
        for i in 0..rhs.len() {
            neg_rhs[i] = T::default().sub(rhs[i]);
        }

        return self.clone()
            + (Polynomial {
                coefficients: neg_rhs,
            });
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Sub<T> for Polynomial<T> {
    type Output = Self;

    fn sub(self, other: T) -> Self {
        let mut c = self.coefficients;
        c[usize::zero()] = c[usize::zero()] - other;
        Polynomial { coefficients: c }
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Mul<Polynomial<T>> for Polynomial<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let lhs = self.coefficients;
        let rhs = rhs.coefficients;
        let mut result = Seq::<T>::create(lhs.len() + rhs.len());
        for i in 0..lhs.len() {
            if !lhs[i].equal(T::default()) {
                for j in 0..rhs.len() {
                    if !rhs[j].equal(T::default()) {
                        result[i + j] = (result[i + j].add(lhs[i] * rhs[j]));
                    }
                }
            }
        }
        (Polynomial {
            coefficients: result,
        })
        .trim()
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Mul<T> for Polynomial<T> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self::Output {
        let mut c = self.coefficients;
        for i in 0..c.len() {
            c[i] = c[i] * rhs;
        }
        Polynomial { coefficients: c }
    }
}

impl<T: Numeric + NumericCopy + PartialEq + hacspec_lib::Div<Output = T>> Div<Polynomial<T>>
    for Polynomial<T>
{
    type Output = (Self, Self);

    fn div(self, rhs: Self) -> Self::Output {
        let mut q = Polynomial::<T>::default();
        let mut r = self.clone();

        if rhs.degree() > self.degree() {
            return (q.trim(), r.trim());
        }

        let mut loop_upper_bound = rhs.degree();
        if self.degree() > rhs.degree() {
            loop_upper_bound = self.degree();
        }

        for _ in 0..loop_upper_bound {
            if r.trim() != Polynomial::<T>::default() && r.degree() >= rhs.degree() {
                let degree_diff = r.degree() - rhs.degree();
                let mut t = Seq::<T>::create(degree_diff + usize::one());
                t[degree_diff] = r.leading_term() / rhs.leading_term();
                let t = Polynomial { coefficients: t };

                q = q + t.clone();
                let aux_prod = rhs.clone() * t;
                r = r - aux_prod;
            }
        }

        (q.trim(), r.trim())
    }
}

impl<T: Numeric + NumericCopy + PartialEq + hacspec_lib::Div<Output = T>> Div<T> for Polynomial<T> {
    type Output = Self;

    fn div(self, rhs: T) -> Self {
        let mut c = self.coefficients;
        for i in 0..c.len() {
            c[i] = c[i] / rhs;
        }
        Polynomial { coefficients: c }
    }
}

impl<T: Numeric + NumericCopy + PartialEq> PartialEq for Polynomial<T> {
    fn eq(&self, other: &Self) -> bool {
        let lhs = &self.trim().coefficients;
        let rhs = &other.trim().coefficients;

        if lhs.len() != rhs.len() {
            return false;
        } else {
            for i in 0..lhs.len() {
                if lhs[i] != rhs[i] {
                    return false;
                }
            }
        }
        true
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Default for Polynomial<T> {
    /// Constant polynomial with value T::default
    fn default() -> Self {
        Polynomial {
            coefficients: Seq::<T>::create(1),
        }
    }
}

// TESTS

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;

#[cfg(test)] // as to not export it
public_nat_mod!(
    type_name: FpPallas,
    type_of_canvas: PallasCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC094CF91B992D30ED00000001"
);

impl<T: Numeric + NumericCopy> Clone for Polynomial<T> {
    fn clone(&self) -> Self {
        Polynomial {
            coefficients: self.coefficients.clone(),
        }
    }
}

// Only needed for test/Arbitrary (and mut refs are not supported)
#[cfg(test)]
impl<T: Numeric + NumericCopy> Debug for Polynomial<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

#[cfg(test)]
impl<T: Numeric + NumericCopy> Display for Polynomial<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

#[cfg(test)]
impl Arbitrary for Polynomial<FpPallas> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Polynomial<FpPallas> {
        let size = usize::arbitrary(g) % 20 + 1;
        let mut v: Vec<FpPallas> = vec![];
        for _ in 0..size {
            let new_val = FpPallas::from_literal(u128::arbitrary(g));
            v.push(new_val);
        }
        Polynomial {
            coefficients: Seq::from_vec(v),
        }
    }
}

// For testing, a constant polynomial with value 1
#[cfg(test)]
fn constant_one_poly_pallas() -> Polynomial<FpPallas> {
    let mut c = Seq::<FpPallas>::create(1);
    c[usize::zero()] = FpPallas::ONE();
    Polynomial { coefficients: c }
}

// Addition

#[cfg(test)]
#[quickcheck]
fn test_poly_add_logic(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: usize) {
    let x = FpPallas::from_literal(x as u128);
    let sum_poly = p1.clone() + p2.clone();

    let expected = p1.evaluate(x) + p2.evaluate(x);
    let actual = sum_poly.evaluate(x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_closure(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>) {
    let p3 = p1 + p2;
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_associativity(
    p1: Polynomial<FpPallas>,
    p2: Polynomial<FpPallas>,
    p3: Polynomial<FpPallas>,
) {
    let p4 = p1.clone() + p2.clone();
    let p4 = p4.clone() + p3.clone();
    let p5 = p2.clone() + p3.clone();
    let p5 = p5.clone() + p1.clone();
    assert_eq!(p4, p5);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_identity(p1: Polynomial<FpPallas>) {
    let p2 = p1.clone() + Polynomial::<FpPallas>::default();

    let p3 = Polynomial::<FpPallas>::default() + p1.clone();
    assert_eq!(p1, p2);
    assert_eq!(p3, p2);
}

// Subtraction

#[cfg(test)]
#[quickcheck]
fn test_poly_sub(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: u128) {
    let x = FpPallas::from_literal(x);
    let sum_poly = p1.clone() - p2.clone();

    let expected = p1.evaluate(x) - p2.evaluate(x);
    let actual = sum_poly.evaluate(x);
    assert_eq!(expected, actual);
}

// Addition / Subtraction

#[cfg(test)]
#[quickcheck]
fn test_poly_add_inverse(p1: Polynomial<FpPallas>) {
    let p1_inv = Polynomial::<FpPallas>::default() - p1.clone();
    let p3 = p1.clone() + p1_inv.clone();
    let p4 = p1_inv + p1;
    assert_eq!(p3, p4);
    assert_eq!(p3, Polynomial::<FpPallas>::default());
}

// Multiplication

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_logic(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: u128) {
    let x = FpPallas::from_literal(x);
    let mul_poly = p1.clone() * p2.clone();

    let expected = p1.evaluate(x) * p2.evaluate(x);
    let actual = mul_poly.evaluate(x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_closure(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>) {
    let p3 = p1 * p2;
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_associativity(
    p1: Polynomial<FpPallas>,
    p2: Polynomial<FpPallas>,
    p3: Polynomial<FpPallas>,
) {
    let p4 = p1.clone() * p2.clone();
    let p4 = p4.clone() * p3.clone();
    let p5 = p2.clone() * p3.clone();
    let p5 = p5.clone() * p1.clone();
    assert_eq!(p4, p5);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_identity(p1: Polynomial<FpPallas>) {
    let mut const_one_poly = constant_one_poly_pallas();

    let p2 = p1.clone() * const_one_poly.clone();
    let p3 = const_one_poly.clone() * p1.clone();

    assert_eq!(p1, p2);
    assert_eq!(p2, p3);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_cummutativity(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>) {
    let p3 = p1.clone() * p2.clone();
    let p4 = p2 * p1.clone();
    assert_eq!(p3, p4);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_left_distributive(
    p1: Polynomial<FpPallas>,
    p2: Polynomial<FpPallas>,
    p3: Polynomial<FpPallas>,
) {
    let p4 = p1.clone() * (p2.clone() + p3.clone());
    let p5 = (p1.clone() * p2) + (p1 * p3);
    assert_eq!(p4, p5);
}

// Division

#[cfg(test)]
#[quickcheck]
fn test_poly_div(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: u128) {
    if p2.degree() > 0 {
        let x = FpPallas::from_literal(x);

        let (q, r) = p1.clone() / p2.clone();
        let eval_q = q.evaluate(x);
        let eval_r = r.evaluate(x);
        let eval_p1 = p1.evaluate(x);
        let eval_p2 = p2.evaluate(x);
        let eval_r_div = eval_r / eval_p2;

        let expected = eval_p1 / eval_p2;
        let actual = eval_q + eval_r_div;

        assert_eq!(expected, actual);
    }
}

// Scalar tests

#[cfg(test)]
#[quickcheck]
fn test_scalar_add(p: Polynomial<FpPallas>, x: u128, scalar: u128) {
    let x = FpPallas::from_literal(x);
    let scalar = FpPallas::from_literal(scalar);
    let p_modified = p.clone() + scalar;
    let p_eval = p.evaluate(x);
    let p_modified_eval = p_modified.evaluate(x);
    assert_eq!(p_eval + scalar, p_modified_eval);
}

#[cfg(test)]
#[quickcheck]
fn test_scalar_sub(p: Polynomial<FpPallas>, x: u128, scalar: u128) {
    let x = FpPallas::from_literal(x);
    let scalar = FpPallas::from_literal(scalar);
    let p_modified = p.clone() - scalar;
    let p_eval = p.evaluate(x);
    let p_modified_eval = p_modified.evaluate(x);
    assert_eq!(p_eval - scalar, p_modified_eval);
}

#[cfg(test)]
#[quickcheck]
fn test_scalar_mul(p: Polynomial<FpPallas>, x: u128, scalar: u128) {
    let x = FpPallas::from_literal(x);
    let scalar = FpPallas::from_literal(scalar);
    let p_modified = p.clone() * scalar;
    let p_eval = p.evaluate(x);
    let p_modified_eval = p_modified.evaluate(x);
    assert_eq!(p_eval * scalar, p_modified_eval);
}

#[cfg(test)]
#[quickcheck]
fn test_scalar_div(p: Polynomial<FpPallas>, x: u128, scalar: u128) {
    let x = FpPallas::from_literal(x);
    let scalar = FpPallas::from_literal(scalar);
    let p_modified = p.clone() / scalar;
    let p_eval = p.evaluate(x);
    let p_modified_eval = p_modified.evaluate(x);
    assert_eq!(p_eval / scalar, p_modified_eval);
}

