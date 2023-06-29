use natmod::nat_mod;

/// This has to come from the lib.
pub trait NatMod<T> {
    const MODULUS: T;
    const MODULUS_STR: &'static str;
}

#[nat_mod("03fffffffffffffffffffffffffffffffb", 17)]
struct FieldElement {}

#[test]
fn add() {
    let x = FieldElement::from_hex("03fffffffffffffffffffffffffffffffa");
    let y = FieldElement::from_hex("01");
    let z = x + y;
    assert_eq!(FieldElement::zero().as_ref(), z.as_ref());

    let x = FieldElement::from_hex("03fffffffffffffffffffffffffffffffa");
    let y = FieldElement::from_hex("02");
    let z = x + y;
    assert_eq!(FieldElement::from_hex("01").as_ref(), z.as_ref());
}

#[test]
fn mul() {
    let x = FieldElement::from_hex("03fffffffffffffffffffffffffffffffa");
    let y = FieldElement::from_hex("01");
    let z = x * y;
    assert_eq!(x.as_ref(), z.as_ref());

    let x = FieldElement::from_hex("03fffffffffffffffffffffffffffffffa");
    let y = FieldElement::from_hex("02");
    let z = x * y;
    assert_eq!(
        FieldElement::from_hex("03fffffffffffffffffffffffffffffff9").as_ref(),
        z.as_ref()
    );
}
