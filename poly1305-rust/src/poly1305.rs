// WARNING:
// This spec does not provide secret independence, and treats all keys as public.
// Consequently, it should only be used as a FORMAL SPEC, NOT as a reference implementation.

mod hacspec_helper;
use hacspec_helper::*;
use natmod::nat_mod;

// Type definitions for use in poly1305.
pub type PolyKey = [u8; 32];

const BLOCKSIZE: usize = 16;

// These are type aliases for convenience
pub type PolyBlock = [u8; BLOCKSIZE];

// These are actual types; fixed-length arrays.
type Poly1305Tag = [u8; BLOCKSIZE];

// A byte sequence of length <= BLOCKSIZE
pub type SubBlock = Vec<u8>;

// A length <= BLOCKSIZE
pub type BlockIndex = usize;

// This defines the field for modulo 2^130-5.
// In particular `FieldElement` and `FieldCanvas` are defined.
// The `FieldCanvas` is an integer type with 131-bit (to hold 2*(2^130-5)).
// The `FieldElement` is a natural integer modulo 2^130-5.
#[nat_mod("03fffffffffffffffffffffffffffffffb", 17)]
struct FieldElement {}

// Internal Poly1305 State
pub struct PolyState {
    acc: FieldElement,
    r: FieldElement,
    key: PolyKey,
}

pub fn poly1305_encode_r(b: PolyBlock) -> FieldElement {
    let mut n = u128::from_le_bytes(b);
    n = n & 0x0fff_fffc_0fff_fffc_0fff_fffc_0fff_ffffu128;
    FieldElement::from_u128(n)
}

pub fn poly1305_encode_block(b: PolyBlock) -> FieldElement {
    let f = FieldElement::from_le_bytes(&b);
    f + FieldElement::pow2(128)
}

// In Poly1305 as used in this spec, pad_len is always the length of b, i.e. there is no padding
// In Chacha20Poly1305, pad_len is set to BLOCKSIZE
pub fn poly1305_encode_last(pad_len: BlockIndex, b: &[u8]) -> FieldElement {
    let f = FieldElement::from_le_bytes(b);
    f + FieldElement::pow2(8 * pad_len)
}

pub fn poly1305_init(key: PolyKey) -> PolyState {
    let r = poly1305_encode_r(key[0..16].try_into().unwrap());
    PolyState {
        acc: FieldElement::zero(),
        r,
        key,
    }
}

pub fn poly1305_update_block(b: PolyBlock, mut st: PolyState) -> PolyState {
    st.acc = (poly1305_encode_block(b) + st.acc) * st.r;
    st
}

pub fn poly1305_update_blocks(m: &[u8], mut st: PolyState) -> PolyState {
    for chunk in m.chunks_exact(BLOCKSIZE) {
        st = poly1305_update_block(chunk.try_into().unwrap(), st);
    }
    st
}

pub fn poly1305_update_last(pad_len: usize, b: &[u8], st: PolyState) -> PolyState {
    let mut st = st;
    if b.len() != 0 {
        st.acc = (poly1305_encode_last(pad_len, b) + st.acc) * st.r;
    }
    st
}

pub fn poly1305_update(m: &[u8], st: PolyState) -> PolyState {
    let st = poly1305_update_blocks(m, st);
    let last = m.chunks_exact(BLOCKSIZE).remainder();
    poly1305_update_last(last.len(), last, st)
}

pub fn poly1305_finish(st: PolyState) -> Poly1305Tag {
    let n = u128::from_le_bytes(st.key[16..32].try_into().unwrap());
    let aby = st.acc.to_le_bytes();
    let a = u128::from_le_bytes(aby[0..16].try_into().unwrap());
    (a.wrapping_add(n)).to_le_bytes()
}

pub fn poly1305(m: &[u8], key: PolyKey) -> Poly1305Tag {
    let mut st = poly1305_init(key);
    st = poly1305_update(m, st);
    poly1305_finish(st)
}
