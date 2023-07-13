module Curve25519
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_X25519FieldElement = { f_value:array u8 32sz }

type t_Scalar = { f_value:array u8 32sz }

let t_Point = (t_X25519FieldElement & t_X25519FieldElement)

let t_X25519SerializedPoint = array u8 32sz

let t_X25519SerializedScalar = array u8 32sz

let mask_scalar (s: array u8 32sz) : array u8 32sz =
  let k:array u8 32sz = s in
  let k:array u8 32sz =
    Rust_primitives.Hax.update_at k
      0sz
      ((k.[ 0sz ] <: u8) &. (Curve25519.Hacspec_helper.v_U8 248uy <: u8) <: u8)
  in
  let k:array u8 32sz =
    Rust_primitives.Hax.update_at k
      31sz
      ((k.[ 31sz ] <: u8) &. (Curve25519.Hacspec_helper.v_U8 127uy <: u8) <: u8)
  in
  let k:array u8 32sz =
    Rust_primitives.Hax.update_at k
      31sz
      ((k.[ 31sz ] <: u8) |. (Curve25519.Hacspec_helper.v_U8 64uy <: u8) <: u8)
  in
  k

let decode_scalar (s: array u8 32sz) : t_Scalar =
  let k:array u8 32sz = mask_scalar s in
  Curve25519.Hacspec_helper.NatMod.from_le_bytes (Rust_primitives.unsize k <: slice u8)

let decode_point (u: array u8 32sz) : (t_X25519FieldElement & t_X25519FieldElement) =
  let u:array u8 32sz =
    Rust_primitives.Hax.update_at u
      31sz
      ((u.[ 31sz ] <: u8) &. (Curve25519.Hacspec_helper.v_U8 127uy <: u8) <: u8)
  in
  Curve25519.Hacspec_helper.NatMod.from_le_bytes (Rust_primitives.unsize u <: slice u8),
  Curve25519.Hacspec_helper.NatMod.from_u128 (pub_u128 1sz)

let encode_point (p: (t_X25519FieldElement & t_X25519FieldElement)) : array u8 32sz =
  let b = p._1 *. (Curve25519.Hacspec_helper.NatMod.inv p._2 <: t_X25519FieldElement) in
  Curve25519.Hacspec_helper.NatMod.to_le_bytes b

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
  let x_1_, v__z_1_:(t_X25519FieldElement & t_X25519FieldElement) = q in
  let x_2_, z_2_:(t_X25519FieldElement & t_X25519FieldElement) = nq in
  let x_3_, z_3_:(t_X25519FieldElement & t_X25519FieldElement) = nqp1 in
  let a = x_2_ +. z_2_ in
  let aa:t_X25519FieldElement = Curve25519.Hacspec_helper.NatMod.pow a (pub_u128 2sz) in
  let b = x_2_ -. z_2_ in
  let bb = b *. b in
  let e = aa -. bb in
  let c = x_3_ +. z_3_ in
  let d = x_3_ -. z_3_ in
  let da = d *. a in
  let cb = c *. b in
  let x_3_:t_X25519FieldElement =
    Curve25519.Hacspec_helper.NatMod.pow (da +. cb <: _) (pub_u128 2sz)
  in
  let z_3_ =
    x_1_ *.
    (Curve25519.Hacspec_helper.NatMod.pow (da -. cb <: _) (pub_u128 2sz) <: t_X25519FieldElement)
  in
  let x_2_ = aa *. bb in
  let e121665:t_X25519FieldElement =
    Curve25519.Hacspec_helper.NatMod.from_u128 (pub_u128 121665sz)
  in
  let z_2_ = e *. (aa +. (e121665 *. e <: _) <: _) in
  FStar.Pervasives.Native.Mktuple2 x_2_ z_2_, FStar.Pervasives.Native.Mktuple2 x_3_ z_3_

let swap
      (x:
          ((t_X25519FieldElement & t_X25519FieldElement) &
            (t_X25519FieldElement & t_X25519FieldElement)))
    : ((t_X25519FieldElement & t_X25519FieldElement) & (t_X25519FieldElement & t_X25519FieldElement)
    ) = x._2, x._1

let montgomery_ladder (k: t_Scalar) (init: (t_X25519FieldElement & t_X25519FieldElement))
    : (t_X25519FieldElement & t_X25519FieldElement) =
  let inf:(t_X25519FieldElement & t_X25519FieldElement) =
    Curve25519.Hacspec_helper.NatMod.from_u128 (pub_u128 1sz),
    Curve25519.Hacspec_helper.NatMod.from_u128 (pub_u128 0sz)
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
              Core.Ops.Range.Range.f_start = pub_u128 0sz;
              Core.Ops.Range.Range.f_end = pub_u128 256sz
            })
        <:
        _)
      acc
      (fun acc i ->
          if Curve25519.Hacspec_helper.NatMod.bit k (pub_u128 255sz -. i <: u128) <: bool
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
  acc._1

let x25519_scalarmult (s p: array u8 32sz) : array u8 32sz =
  let s:t_Scalar = decode_scalar s in
  let p:(t_X25519FieldElement & t_X25519FieldElement) = decode_point p in
  let r:(t_X25519FieldElement & t_X25519FieldElement) = montgomery_ladder s p in
  encode_point r

let x25519_secret_to_public (s: array u8 32sz) : array u8 32sz =
  let base:array u8 32sz = Rust_primitives.Hax.repeat 0uy 32sz in
  let base:array u8 32sz =
    Rust_primitives.Hax.update_at base 0sz (Curve25519.Hacspec_helper.v_U8 9uy <: u8)
  in
  x25519_scalarmult s base