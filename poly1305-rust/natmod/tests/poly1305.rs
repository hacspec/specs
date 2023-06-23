use natmod::nat_mod;

/// This has to come from the lib.
pub trait NatMod<T> {
    const MODULUS: T;
}

#[nat_mod("03fffffffffffffffffffffffffffffffb", 17)]
struct FieldElement {}

#[test]
fn natmod() {
    let x = FieldElement::from_hex("03fffffffffffffffffffffffffffffffa");
    let y = FieldElement::from_hex("01");
    let z = x + y;
    assert_eq!(FieldElement::zero().as_ref(), z.as_ref());
}
