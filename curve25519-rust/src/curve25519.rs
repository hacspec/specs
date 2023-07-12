mod hacspec_helper;
use hacspec_helper::*;

#[nat_mod("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed", 32)]
pub struct X25519FieldElement {}

#[nat_mod("8000000000000000000000000000000000000000000000000000000000000000", 32)]
pub struct Scalar {}

pub type Point = (X25519FieldElement, X25519FieldElement);

pub type X25519SerializedPoint = [U8; 32];
pub type X25519SerializedScalar = [U8; 32];

fn mask_scalar(s: X25519SerializedScalar) -> X25519SerializedScalar {
    let mut k = s;
    k[0] = k[0] & U8(248);
    k[31] = k[31] & U8(127);
    k[31] = k[31] | U8(64);
    k
}

fn decode_scalar(s: X25519SerializedScalar) -> Scalar {
    let k = mask_scalar(s);
    Scalar::from_le_bytes(&k)
}

fn decode_point(u: X25519SerializedPoint) -> Point {
    let mut u_ = u;
    u_[31] = u_[31] & U8(127u8);
    (
        X25519FieldElement::from_le_bytes(&u_),
        X25519FieldElement::from_u128(1),
    )
}

fn encode_point(p: Point) -> X25519SerializedPoint {
    let (x, y) = p;
    let b = x * y.inv();
    b.to_le_bytes()
}

fn point_add_and_double(q: Point, np: (Point, Point)) -> (Point, Point) {
    let (nq, nqp1) = np;
    let (x_1, _z_1) = q;
    let (x_2, z_2) = nq;
    let (x_3, z_3) = nqp1;
    let a = x_2 + z_2;
    let aa = a.pow(2);
    let b = x_2 - z_2;
    let bb = b * b;
    let e = aa - bb;
    let c = x_3 + z_3;
    let d = x_3 - z_3;
    let da = d * a;
    let cb = c * b;

    let x_3 = (da + cb).pow(2u128);
    let z_3 = x_1 * ((da - cb).pow(2u128));
    let x_2 = aa * bb;
    let e121665 = X25519FieldElement::from_u128(121_665);
    let z_2 = e * (aa + (e121665 * e));
    ((x_2, z_2), (x_3, z_3))
}

fn swap(x: (Point, Point)) -> (Point, Point) {
    let (x0, x1) = x;
    (x1, x0)
}

fn montgomery_ladder(k: Scalar, init: Point) -> Point {
    let inf = (
        X25519FieldElement::from_u128(1),
        X25519FieldElement::from_u128(0),
    );
    let mut acc: (Point, Point) = (inf, init);
    for i in 0..256 {
        if k.bit(255 - i) {
            acc = swap(acc);
            acc = point_add_and_double(init, acc);
            acc = swap(acc);
        } else {
            acc = point_add_and_double(init, acc);
        }
    }
    let (out, _) = acc;
    out
}

pub fn x25519_scalarmult(
    s: X25519SerializedScalar,
    p: X25519SerializedPoint,
) -> X25519SerializedPoint {
    let s_ = decode_scalar(s);
    let p_ = decode_point(p);
    let r = montgomery_ladder(s_, p_);
    encode_point(r)
}

pub fn x25519_secret_to_public(s: X25519SerializedScalar) -> X25519SerializedPoint {
    let mut base = [0; 32];
    base[0] = U8(0x09u8);
    x25519_scalarmult(s, base)
}
