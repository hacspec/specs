module Hacspec_edwards25519
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_ed25519fieldelement =
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
unfold
type t_fieldcanvas = lseq pub_uint8 256

unfold
type t_scalar = nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
unfold
type t_scalarcanvas = lseq pub_uint8 256

unfold
type t_bigscalar = nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
unfold
type t_bigscalarcanvas = lseq pub_uint8 512

unfold
type t_biginteger = nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000
unfold
type t_bigintegercanvas = lseq pub_uint8 256

let t_EdPoint =
  (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement)

unfold
type t_compressededpoint = lseq uint8 32

unfold
type t_serializedscalar = lseq uint8 32

unfold
type t_signature = lseq uint8 64

let t_PublicKey = t_CompressedEdPoint

let t_SecretKey = t_SerializedScalar

type t_Error =
  | Error_InvalidPublickey : t_Error
  | Error_InvalidSignature : t_Error
  | Error_InvalidS : t_Error
  | Error_InvalidR : t_Error
  | Error_SmallOrderPoint : t_Error
  | Error_NotEnoughRandomness : t_Error

let t_VerifyResult = Core.Result.t_Result Prims.unit t_Error

let v_BASE: t_CompressedEdPoint =
  CompressedEdPoint
  (let l =
      [
        Secret_integers.U8 88uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy; Secret_integers.U8 102uy;
        Secret_integers.U8 102uy; Secret_integers.U8 102uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let v_CONSTANT_P: t_SerializedScalar =
  SerializedScalar
  (let l =
      [
        Secret_integers.U8 237uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 127uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let v_CONSTANT_L: t_SerializedScalar =
  SerializedScalar
  (let l =
      [
        Secret_integers.U8 237uy; Secret_integers.U8 211uy; Secret_integers.U8 245uy;
        Secret_integers.U8 92uy; Secret_integers.U8 26uy; Secret_integers.U8 99uy;
        Secret_integers.U8 18uy; Secret_integers.U8 88uy; Secret_integers.U8 214uy;
        Secret_integers.U8 156uy; Secret_integers.U8 247uy; Secret_integers.U8 162uy;
        Secret_integers.U8 222uy; Secret_integers.U8 249uy; Secret_integers.U8 222uy;
        Secret_integers.U8 20uy; Secret_integers.U8 0uy; Secret_integers.U8 0uy;
        Secret_integers.U8 0uy; Secret_integers.U8 0uy; Secret_integers.U8 0uy;
        Secret_integers.U8 0uy; Secret_integers.U8 0uy; Secret_integers.U8 0uy;
        Secret_integers.U8 0uy; Secret_integers.U8 0uy; Secret_integers.U8 0uy;
        Secret_integers.U8 0uy; Secret_integers.U8 0uy; Secret_integers.U8 0uy;
        Secret_integers.U8 0uy; Secret_integers.U8 16uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let v_CONSTANT_P3_8_: t_SerializedScalar =
  SerializedScalar
  (let l =
      [
        Secret_integers.U8 254uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 15uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let v_CONSTANT_P1_4_: t_SerializedScalar =
  SerializedScalar
  (let l =
      [
        Secret_integers.U8 251uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 255uy; Secret_integers.U8 255uy;
        Secret_integers.U8 255uy; Secret_integers.U8 31uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let v_CONSTANT_D: t_SerializedScalar =
  SerializedScalar
  (let l =
      [
        Secret_integers.U8 163uy; Secret_integers.U8 120uy; Secret_integers.U8 89uy;
        Secret_integers.U8 19uy; Secret_integers.U8 202uy; Secret_integers.U8 77uy;
        Secret_integers.U8 235uy; Secret_integers.U8 117uy; Secret_integers.U8 171uy;
        Secret_integers.U8 216uy; Secret_integers.U8 65uy; Secret_integers.U8 65uy;
        Secret_integers.U8 77uy; Secret_integers.U8 10uy; Secret_integers.U8 112uy;
        Secret_integers.U8 0uy; Secret_integers.U8 152uy; Secret_integers.U8 232uy;
        Secret_integers.U8 121uy; Secret_integers.U8 119uy; Secret_integers.U8 121uy;
        Secret_integers.U8 64uy; Secret_integers.U8 199uy; Secret_integers.U8 140uy;
        Secret_integers.U8 115uy; Secret_integers.U8 254uy; Secret_integers.U8 111uy;
        Secret_integers.U8 43uy; Secret_integers.U8 238uy; Secret_integers.U8 108uy;
        Secret_integers.U8 3uy; Secret_integers.U8 82uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let is_negative (x: t_Ed25519FieldElement) : Secret_integers.t_U8 =
  if bit_under_impl_63 x 0sz then Secret_integers.U8 1uy else Secret_integers.U8 0uy

let compress
      (p:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : t_CompressedEdPoint =
  let x, y, z, _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    p
  in
  let z_inv:t_Ed25519FieldElement = inv_under_impl_57 z in
  let x = x *. z_inv in
  let y = y *. z_inv in
  let (s: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8):Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    to_byte_seq_le_under_impl y
  in
  let s:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at s 31l (s.[ 31l ] ^. (is_negative x >>. 7sz))
  in
  from_slice_under_impl_274 s 0sz 32sz

let sqrt (a: t_Ed25519FieldElement) : Core.Option.t_Option t_Ed25519FieldElement =
  let p3_8:t_Ed25519FieldElement = from_byte_seq_le_under_impl v_CONSTANT_P3_8_ in
  let p1_4:t_Ed25519FieldElement = from_byte_seq_le_under_impl v_CONSTANT_P1_4_ in
  let x_c:t_Ed25519FieldElement = Hacspec_lib.Traits.Numeric.pow_self a p3_8 in
  let (result: Core.Option.t_Option t_Ed25519FieldElement):Core.Option.t_Option
  t_Ed25519FieldElement =
    Core.Option.Option_None
  in
  let result:Core.Option.t_Option t_Ed25519FieldElement =
    if x_c *. x_c =. a
    then
      let result:Core.Option.t_Option t_Ed25519FieldElement = Core.Option.Option_Some x_c in
      result
    else result
  in
  let result:Core.Option.t_Option t_Ed25519FieldElement =
    if x_c *. x_c =. Hacspec_lib.Traits.Integer.v_ZERO -. a
    then
      let x = Hacspec_lib.Traits.Numeric.pow_self Hacspec_lib.Traits.Integer.v_TWO p1_4 *. x_c in
      let result:Core.Option.t_Option t_Ed25519FieldElement = Core.Option.Option_Some x in
      result
    else result
  in
  result

let check_canonical_point (x: t_CompressedEdPoint) : bool =
  let x:t_CompressedEdPoint =
    Rust_primitives.Hax.update_at x 31l (x.[ 31l ] &. Secret_integers.U8 127uy)
  in
  let x:t_BigInteger = from_byte_seq_le_under_impl_201 x in
  x <. from_byte_seq_le_under_impl_201 v_CONSTANT_P

let decompress (q: t_CompressedEdPoint)
    : Core.Option.t_Option
    (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement) =
  Rust_primitives.Hax.Control_flow_monad.Moption.run (let d:t_Ed25519FieldElement =
        from_byte_seq_le_under_impl v_CONSTANT_D
      in
      let x_s = (q.[ 31sz ] &. Secret_integers.U8 128uy) <<. 7sz in
      let y_s:t_CompressedEdPoint = q in
      let y_s:t_CompressedEdPoint =
        Rust_primitives.Hax.update_at y_s 31l (y_s.[ 31l ] &. Secret_integers.U8 127uy)
      in
      let* _:Prims.unit =
        if ~.(check_canonical_point y_s)
        then
          let* _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement) =
            Core.Option.Option_None
          in
          Core.Option.Option_Some ()
        else Core.Option.Option_Some ()
      in
      let y:t_Ed25519FieldElement = from_byte_seq_le_under_impl y_s in
      let z:t_Ed25519FieldElement = Hacspec_lib.Traits.Integer.v_ONE in
      let yy = y *. y in
      let u = yy -. z in
      let v = d *. yy +. z in
      let xx = u *. inv_under_impl_57 v in
      let x:Core.Option.t_Option
      (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement
      ) =
        Core.Ops.Try_trait.FromResidual.from_residual (sqrt xx)
      in
      let x_r:Secret_integers.t_U8 = is_negative x in
      let* _:Prims.unit =
        if
          Prims.op_AmpAmp (x =. Hacspec_lib.Traits.Integer.v_ZERO)
            (Secret_integers.declassify_under_impl_2 x_s =. 1uy)
        then
          let* _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement) =
            Core.Option.Option_None
          in
          Core.Option.Option_Some ()
        else Core.Option.Option_Some ()
      in
      Core.Option.Option_Some
      (let x =
          if
            Secret_integers.declassify_under_impl_2 x_r <>.
            Secret_integers.declassify_under_impl_2 x_s
          then
            let x = Hacspec_lib.Traits.Integer.v_ZERO -. x in
            x
          else x
        in
        Core.Option.Option_Some (x, y, z, x *. y)))

let decompress_non_canonical (p: t_CompressedEdPoint)
    : Core.Option.t_Option
    (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement) =
  let d:t_Ed25519FieldElement = from_byte_seq_le_under_impl v_CONSTANT_D in
  let x_s = (p.[ 31sz ] &. Secret_integers.U8 128uy) <<. 7sz in
  let y_s:t_CompressedEdPoint = p in
  let y_s:t_CompressedEdPoint =
    Rust_primitives.Hax.update_at y_s 31l (y_s.[ 31l ] &. Secret_integers.U8 127uy)
  in
  let y:t_Ed25519FieldElement = from_byte_seq_le_under_impl y_s in
  let z:t_Ed25519FieldElement = Hacspec_lib.Traits.Integer.v_ONE in
  let yy = y *. y in
  let u = yy -. z in
  let v = d *. yy +. z in
  let xx = u *. inv_under_impl_57 v in
  let x:Core.Option.t_Option
  (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement) =
    Core.Ops.Try_trait.FromResidual.from_residual (sqrt xx)
  in
  let x_r:Secret_integers.t_U8 = is_negative x in
  let x =
    if Secret_integers.declassify_under_impl_2 x_r <>. Secret_integers.declassify_under_impl_2 x_s
    then
      let x = Hacspec_lib.Traits.Integer.v_ZERO -. x in
      x
    else x
  in
  Core.Option.Option_Some (x, y, z, x *. y)

let encode
      (p:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let x, y, z, _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    p
  in
  let z_inv:t_Ed25519FieldElement = inv_under_impl_57 z in
  let x = x *. z_inv in
  let y = y *. z_inv in
  let (s: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8):Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    to_byte_seq_le_under_impl y
  in
  let s:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at s 31l (s.[ 31l ] ^. (is_negative x >>. 7sz))
  in
  s

let decode (q_s: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Option.t_Option
    (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement) =
  let q:t_CompressedEdPoint = from_slice_under_impl_274 q_s 0sz 32sz in
  decompress q

let point_add
      (p q:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement
    ) =
  let d_c:t_Ed25519FieldElement = from_byte_seq_le_under_impl v_CONSTANT_D in
  let two:t_Ed25519FieldElement = Hacspec_lib.Traits.Integer.v_TWO in
  let x1, y1, z1, t1:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    p
  in
  let x2, y2, z2, t2:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    q
  in
  let a = (y1 -. x1) *. (y2 -. x2) in
  let b = (y1 +. x1) *. (y2 +. x2) in
  let c = t1 *. two *. d_c *. t2 in
  let d = z1 *. two *. z2 in
  let e = b -. a in
  let f = d -. c in
  let g = d +. c in
  let h = b +. a in
  let x3 = e *. f in
  let y3 = g *. h in
  let t3 = e *. h in
  let z3 = f *. g in
  x3, y3, z3, t3

let point_identity: (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
  t_Ed25519FieldElement) =
  Hacspec_lib.Traits.Integer.v_ZERO,
  Hacspec_lib.Traits.Integer.v_ONE,
  Hacspec_lib.Traits.Integer.v_ONE,
  Hacspec_lib.Traits.Integer.v_ZERO

let point_mul
      (s: t_Scalar)
      (p:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement
    ) =
  let p:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    p
  in
  let q:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    point_identity
  in
  let p, q:((t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
      t_Ed25519FieldElement) &
    (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement))
  =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 256sz
            }))
      (p, q)
      (fun (p, q) i ->
          let q:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement) =
            if bit_under_impl_130 s i
            then
              let q:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
                t_Ed25519FieldElement) =
                point_add q p
              in
              q
            else q
          in
          let p:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement) =
            point_add p p
          in
          p, q)
  in
  q

let point_mul_by_cofactor
      (p:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement
    ) =
  let p2:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    point_add p p
  in
  let p4:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    point_add p2 p2
  in
  point_add p4 p4

let point_neg
      (p:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement
    ) =
  let x, y, z, t:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    p
  in
  Hacspec_lib.Traits.Integer.v_ZERO -. x, y, z, Hacspec_lib.Traits.Integer.v_ZERO -. t

let point_eq
      (p q:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : bool =
  let x1, y1, z1, _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    p
  in
  let x2, y2, z2, _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    q
  in
  Prims.op_AmpAmp (x1 *. z2 =. x2 *. z1) (y1 *. z2 =. y2 *. z1)

let point_normalize
      (q:
          (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
            t_Ed25519FieldElement))
    : (t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement
    ) =
  let qx, qy, qz, _:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    q
  in
  let px = qx *. inv_under_impl_57 qz in
  let py = qy *. inv_under_impl_57 qz in
  let pz:t_Ed25519FieldElement = Hacspec_lib.Traits.Integer.v_ONE in
  let pt = px *. py in
  px, py, pz, pt

let secret_expand (sk: t_SerializedScalar) : (t_SerializedScalar & t_SerializedScalar) =
  let h:Hacspec_sha512.t_Sha512Digest =
    Hacspec_sha512.sha512 (Hacspec_lib.Seq.from_slice_under_impl_41 sk 0sz 32sz)
  in
  let h_d:t_SerializedScalar = from_slice_under_impl_309 h 32sz 32sz in
  let s:t_SerializedScalar = from_slice_under_impl_309 h 0sz 32sz in
  let s:t_SerializedScalar =
    Rust_primitives.Hax.update_at s 0l (s.[ 0l ] &. Secret_integers.U8 248uy)
  in
  let s:t_SerializedScalar =
    Rust_primitives.Hax.update_at s 31l (s.[ 31l ] &. Secret_integers.U8 127uy)
  in
  let s:t_SerializedScalar =
    Rust_primitives.Hax.update_at s 31l (s.[ 31l ] |. Secret_integers.U8 64uy)
  in
  s, h_d

let secret_to_public (sk: t_SerializedScalar) : t_CompressedEdPoint =
  let s, _:(t_SerializedScalar & t_SerializedScalar) = secret_expand sk in
  let base:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    Core.Option.unwrap_under_impl (decompress v_BASE)
  in
  let ss:t_Scalar = from_byte_seq_le_under_impl_67 s in
  let a:(t_Ed25519FieldElement & t_Ed25519FieldElement & t_Ed25519FieldElement &
    t_Ed25519FieldElement) =
    point_mul ss base
  in
  compress a

let check_canonical_scalar (s: t_SerializedScalar) : bool =
  if Secret_integers.declassify_under_impl_2 (s.[ 31sz ] &. Secret_integers.U8 224uy) <>. 0uy
  then false
  else from_byte_seq_le_under_impl_201 s <. from_byte_seq_le_under_impl_201 v_CONSTANT_L