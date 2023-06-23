use num_bigint::BigUint;

pub struct NatMod<const L: usize> {
    value: BigUint,
    modulus: BigUint,
}
