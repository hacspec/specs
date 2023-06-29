/// This has to come from the lib.
pub trait NatMod<T> {
    const MODULUS: T;
    const MODULUS_STR: &'static str;
}
