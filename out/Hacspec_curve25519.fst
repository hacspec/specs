module Hacspec_curve25519
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_x25519fieldelement =
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
unfold
type t_fieldcanvas = lseq pub_uint8 256

unfold
type t_scalar = nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000
unfold
type t_scalarcanvas = lseq pub_uint8 256

let t_Point = (t_X25519FieldElement & t_X25519FieldElement)

unfold
type t_x25519serializedpoint = lseq uint8 32

unfold
type t_x25519serializedscalar = lseq uint8 32

let mask_scalar (s: t_X25519SerializedScalar) : t_X25519SerializedScalar =
  let k:t_X25519SerializedScalar = s in
  let k:t_X25519SerializedScalar =
    Rust_primitives.Hax.update_at k 0l (k.[ 0l ] &. Secret_integers.U8 248uy)
  in
  let k:t_X25519SerializedScalar =
    Rust_primitives.Hax.update_at k 31l (k.[ 31l ] &. Secret_integers.U8 127uy)
  in
  let k:t_X25519SerializedScalar =
    Rust_primitives.Hax.update_at k 31l (k.[ 31l ] |. Secret_integers.U8 64uy)
  in
  k

let decode_scalar (s: t_X25519SerializedScalar) : t_Scalar =
  let k:t_X25519SerializedScalar = mask_scalar s in
  from_byte_seq_le_under_impl_67 k

let decode_point (u: t_X25519SerializedPoint) : (t_X25519FieldElement & t_X25519FieldElement) =
  let u_:t_X25519SerializedPoint = u in
  let u_:t_X25519SerializedPoint =
    Rust_primitives.Hax.update_at u_ 31l (u_.[ 31l ] &. Secret_integers.U8 127uy)
  in
  from_byte_seq_le_under_impl u_, from_literal_under_impl_63 (pub_u128 1sz)

let encode_point (p: (t_X25519FieldElement & t_X25519FieldElement)) : t_X25519SerializedPoint =
  let x, y:(t_X25519FieldElement & t_X25519FieldElement) = p in
  let b = x *. inv_under_impl_57 y in
  Hacspec_lib.Traits.SeqTrait.update_start new_under_impl_139 (to_byte_seq_le_under_impl b)

let point_add_and_double
      (q: (t_X25519FieldElement & t_X25519FieldElement))
      (np:
          ((t_X25519FieldElement & t_X25519FieldElement) &
            (t_X25519FieldElement & t_X25519FieldElement)))
    : ((t_X25519FieldElement & t_X25519FieldElement) & (t_X25519FieldElement & t_X25519FieldElement)
    ) =
  let nq, nqp1:((t_X25519FieldElement & t_X25519FieldElement) &
    (t_X25519FieldElement & t_X25519FieldElement)) =
    np
  in
  let x_1, _z_1:(t_X25519FieldElement & t_X25519FieldElement) = q in
  let x_2, z_2:(t_X25519FieldElement & t_X25519FieldElement) = nq in
  let x_3, z_3:(t_X25519FieldElement & t_X25519FieldElement) = nqp1 in
  let a = x_2 +. z_2 in
  let aa:t_X25519FieldElement = pow_under_impl_57 a (pub_u128 2sz) in
  let b = x_2 -. z_2 in
  let bb = b *. b in
  let e = aa -. bb in
  let c = x_3 +. z_3 in
  let d = x_3 -. z_3 in
  let da = d *. a in
  let cb = c *. b in
  let x_3:t_X25519FieldElement = pow_under_impl_57 (da +. cb) (pub_u128 2sz) in
  let z_3 = x_1 *. pow_under_impl_57 (da -. cb) (pub_u128 2sz) in
  let x_2 = aa *. bb in
  let e121665:t_X25519FieldElement = from_literal_under_impl_63 (pub_u128 121665sz) in
  let z_2 = e *. (aa +. e121665 *. e) in
  FStar.Pervasives.Native.Mktuple2 x_2 z_2, FStar.Pervasives.Native.Mktuple2 x_3 z_3

let swap
      (x:
          ((t_X25519FieldElement & t_X25519FieldElement) &
            (t_X25519FieldElement & t_X25519FieldElement)))
    : ((t_X25519FieldElement & t_X25519FieldElement) & (t_X25519FieldElement & t_X25519FieldElement)
    ) =
  let x0, x1:((t_X25519FieldElement & t_X25519FieldElement) &
    (t_X25519FieldElement & t_X25519FieldElement)) =
    x
  in
  x1, x0

let montgomery_ladder (k: t_Scalar) (init: (t_X25519FieldElement & t_X25519FieldElement))
    : (t_X25519FieldElement & t_X25519FieldElement) =
  let inf:(t_X25519FieldElement & t_X25519FieldElement) =
    from_literal_under_impl_63 (pub_u128 1sz), from_literal_under_impl_63 (pub_u128 0sz)
  in
  let
  (acc:
    ((t_X25519FieldElement & t_X25519FieldElement) & (t_X25519FieldElement & t_X25519FieldElement))):(
    (t_X25519FieldElement & t_X25519FieldElement) & (t_X25519FieldElement & t_X25519FieldElement)) =
    inf, init
  in
  let acc:((t_X25519FieldElement & t_X25519FieldElement) &
    (t_X25519FieldElement & t_X25519FieldElement)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 256sz
            }))
      acc
      (fun acc i ->
          if bit_under_impl_130 k (255sz -. i)
          then
            let acc:((t_X25519FieldElement & t_X25519FieldElement) &
              (t_X25519FieldElement & t_X25519FieldElement)) =
              swap acc
            in
            let acc:((t_X25519FieldElement & t_X25519FieldElement) &
              (t_X25519FieldElement & t_X25519FieldElement)) =
              point_add_and_double init acc
            in
            let acc:((t_X25519FieldElement & t_X25519FieldElement) &
              (t_X25519FieldElement & t_X25519FieldElement)) =
              swap acc
            in
            acc
          else
            let acc:((t_X25519FieldElement & t_X25519FieldElement) &
              (t_X25519FieldElement & t_X25519FieldElement)) =
              point_add_and_double init acc
            in
            acc)
  in
  let out, _:((t_X25519FieldElement & t_X25519FieldElement) &
    (t_X25519FieldElement & t_X25519FieldElement)) =
    acc
  in
  out

let x25519_scalarmult (s: t_X25519SerializedScalar) (p: t_X25519SerializedPoint)
    : t_X25519SerializedPoint =
  let s_:t_Scalar = decode_scalar s in
  let p_:(t_X25519FieldElement & t_X25519FieldElement) = decode_point p in
  let r:(t_X25519FieldElement & t_X25519FieldElement) = montgomery_ladder s_ p_ in
  encode_point r

let x25519_secret_to_public (s: t_X25519SerializedScalar) : t_X25519SerializedPoint =
  let base:t_X25519SerializedPoint = new_under_impl_139 in
  let base:t_X25519SerializedPoint =
    Rust_primitives.Hax.update_at base 0l (Secret_integers.U8 9uy)
  in
  x25519_scalarmult s base