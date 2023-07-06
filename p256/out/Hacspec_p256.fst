module Hacspec_p256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_Error = | Error_InvalidAddition : t_Error

let v_BITS: usize = 256sz

unfold
type t_p256fieldelement = nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
unfold
type t_fieldcanvas = lseq pub_uint8 256

unfold
type t_p256scalar = nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
unfold
type t_scalarcanvas = lseq pub_uint8 256

let t_Affine = (t_P256FieldElement & t_P256FieldElement)

let t_AffineResult = Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error

let t_P256Jacobian = (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement)

let t_JacobianResult =
  Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error

unfold
type t_element = lseq uint8 32

let jacobian_to_affine (p: (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement))
    : (t_P256FieldElement & t_P256FieldElement) =
  let x, y, z:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = p in
  let z2:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp z 2ul in
  let z2i:t_P256FieldElement = inv_under_impl_58 z2 in
  let z3 = z *. z2 in
  let z3i:t_P256FieldElement = inv_under_impl_58 z3 in
  let x = x *. z2i in
  let y = y *. z3i in
  x, y

let affine_to_jacobian (p: (t_P256FieldElement & t_P256FieldElement))
    : (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) =
  let x, y:(t_P256FieldElement & t_P256FieldElement) = p in
  x, y, from_literal_under_impl_64 (pub_u128 1sz)

let point_double (p: (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement))
    : (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) =
  let x1, y1, z1:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = p in
  let delta:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp z1 2ul in
  let gamma:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp y1 2ul in
  let beta = x1 *. gamma in
  let alpha_1 = x1 -. delta in
  let alpha_2 = x1 +. delta in
  let alpha = from_literal_under_impl_64 (pub_u128 3sz) *. (alpha_1 *. alpha_2) in
  let x3 =
    Hacspec_lib.Traits.Numeric.exp alpha 2ul -. from_literal_under_impl_64 (pub_u128 8sz) *. beta
  in
  let z3_:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp (y1 +. z1) 2ul in
  let z3 = z3_ -. (gamma +. delta) in
  let y3_1 = from_literal_under_impl_64 (pub_u128 4sz) *. beta -. x3 in
  let y3_2 = from_literal_under_impl_64 (pub_u128 8sz) *. (gamma *. gamma) in
  let y3 = alpha *. y3_1 -. y3_2 in
  x3, y3, z3

let is_point_at_infinity (p: (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement)) : bool =
  let _x, _y, z:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = p in
  Hacspec_lib.Traits.Numeric.equal z (from_literal_under_impl_64 (pub_u128 0sz))

let s1_equal_s2 (s1 s2: t_P256FieldElement)
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error =
  if Hacspec_lib.Traits.Numeric.equal s1 s2
  then Core.Result.Result.v_Err Error_InvalidAddition
  else
    Core.Result.Result.v_Ok (from_literal_under_impl_64 (pub_u128 0sz),
        from_literal_under_impl_64 (pub_u128 1sz),
        from_literal_under_impl_64 (pub_u128 0sz))

let point_add_jacob (p q: (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement))
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error =
  let result:Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement)
    t_Error =
    Core.Result.Result.v_Ok q
  in
  let result:Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement)
    t_Error =
    if ~.(is_point_at_infinity p)
    then
      if is_point_at_infinity q
      then
        let result:Core.Result.t_Result
          (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error =
          Core.Result.Result.v_Ok p
        in
        result
      else
        let x1, y1, z1:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = p in
        let x2, y2, z2:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = q in
        let z1z1:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp z1 2ul in
        let z2z2:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp z2 2ul in
        let u1 = x1 *. z2z2 in
        let u2 = x2 *. z1z1 in
        let s1 = y1 *. z2 *. z2z2 in
        let s2 = y2 *. z1 *. z1z1 in
        if Hacspec_lib.Traits.Numeric.equal u1 u2
        then
          let result:Core.Result.t_Result
            (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error =
            s1_equal_s2 s1 s2
          in
          result
        else
          let h = u2 -. u1 in
          let i:t_P256FieldElement =
            Hacspec_lib.Traits.Numeric.exp (from_literal_under_impl_64 (pub_u128 2sz) *. h) 2ul
          in
          let j = h *. i in
          let r = from_literal_under_impl_64 (pub_u128 2sz) *. (s2 -. s1) in
          let v = u1 *. i in
          let x3_1 = from_literal_under_impl_64 (pub_u128 2sz) *. v in
          let x3_2 = Hacspec_lib.Traits.Numeric.exp r 2ul -. j in
          let x3 = x3_2 -. x3_1 in
          let y3_1 = from_literal_under_impl_64 (pub_u128 2sz) *. s1 *. j in
          let y3_2 = r *. (v -. x3) in
          let y3 = y3_2 -. y3_1 in
          let z3_:t_P256FieldElement = Hacspec_lib.Traits.Numeric.exp (z1 +. z2) 2ul in
          let z3 = (z3_ -. (z1z1 +. z2z2)) *. h in
          let result:Core.Result.t_Result
            (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error =
            Core.Result.Result.v_Ok (x3, y3, z3)
          in
          result
    else result
  in
  result

let ltr_mul (k: t_P256Scalar) (p: (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement))
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) t_Error =
  let q:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) =
    from_literal_under_impl_64 (pub_u128 0sz),
    from_literal_under_impl_64 (pub_u128 1sz),
    from_literal_under_impl_64 (pub_u128 0sz)
  in
  let q:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_BITS
            }))
      q
      (fun q i ->
          let q:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = point_double q in
          if
            Hacspec_lib.Traits.Numeric.equal (Hacspec_lib.Traits.Integer.get_bit k
                  (v_BITS -. 1sz -. i))
              Hacspec_lib.Traits.Integer.v_ONE
          then
            let* hoist1:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) =
              point_add_jacob q p
            in
            Core.Result.Result_Ok
            (let q:(t_P256FieldElement & t_P256FieldElement & t_P256FieldElement) = hoist1 in
              q)
          else Core.Result.Result_Ok q)
  in
  Core.Result.Result.v_Ok q

let p256_point_mul (k: t_P256Scalar) (p: (t_P256FieldElement & t_P256FieldElement))
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error =
  let jac:Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (ltr_mul k (affine_to_jacobian p))
  in
  Core.Result.Result.v_Ok (jacobian_to_affine jac)

let p256_point_mul_base (k: t_P256Scalar)
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error =
  let base_point:(t_P256FieldElement & t_P256FieldElement) =
    from_byte_seq_be_under_impl_1 (Element
        (let l =
            [
              Secret_integers.U8 107uy; Secret_integers.U8 23uy; Secret_integers.U8 209uy;
              Secret_integers.U8 242uy; Secret_integers.U8 225uy; Secret_integers.U8 44uy;
              Secret_integers.U8 66uy; Secret_integers.U8 71uy; Secret_integers.U8 248uy;
              Secret_integers.U8 188uy; Secret_integers.U8 230uy; Secret_integers.U8 229uy;
              Secret_integers.U8 99uy; Secret_integers.U8 164uy; Secret_integers.U8 64uy;
              Secret_integers.U8 242uy; Secret_integers.U8 119uy; Secret_integers.U8 3uy;
              Secret_integers.U8 125uy; Secret_integers.U8 129uy; Secret_integers.U8 45uy;
              Secret_integers.U8 235uy; Secret_integers.U8 51uy; Secret_integers.U8 160uy;
              Secret_integers.U8 244uy; Secret_integers.U8 161uy; Secret_integers.U8 57uy;
              Secret_integers.U8 69uy; Secret_integers.U8 216uy; Secret_integers.U8 152uy;
              Secret_integers.U8 194uy; Secret_integers.U8 150uy
            ]
          in
          assert_norm (List.Tot.length l == 32);
          Rust_primitives.Hax.array_of_list l)),
    from_byte_seq_be_under_impl_1 (Element
        (let l =
            [
              Secret_integers.U8 79uy; Secret_integers.U8 227uy; Secret_integers.U8 66uy;
              Secret_integers.U8 226uy; Secret_integers.U8 254uy; Secret_integers.U8 26uy;
              Secret_integers.U8 127uy; Secret_integers.U8 155uy; Secret_integers.U8 142uy;
              Secret_integers.U8 231uy; Secret_integers.U8 235uy; Secret_integers.U8 74uy;
              Secret_integers.U8 124uy; Secret_integers.U8 15uy; Secret_integers.U8 158uy;
              Secret_integers.U8 22uy; Secret_integers.U8 43uy; Secret_integers.U8 206uy;
              Secret_integers.U8 51uy; Secret_integers.U8 87uy; Secret_integers.U8 107uy;
              Secret_integers.U8 49uy; Secret_integers.U8 94uy; Secret_integers.U8 206uy;
              Secret_integers.U8 203uy; Secret_integers.U8 182uy; Secret_integers.U8 64uy;
              Secret_integers.U8 104uy; Secret_integers.U8 55uy; Secret_integers.U8 191uy;
              Secret_integers.U8 81uy; Secret_integers.U8 245uy
            ]
          in
          assert_norm (List.Tot.length l == 32);
          Rust_primitives.Hax.array_of_list l))
  in
  p256_point_mul k base_point

let point_add_distinct (p q: (t_P256FieldElement & t_P256FieldElement))
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error =
  let r:Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (point_add_jacob (affine_to_jacobian p)
          (affine_to_jacobian q))
  in
  Core.Result.Result.v_Ok (jacobian_to_affine r)

let point_add (p q: (t_P256FieldElement & t_P256FieldElement))
    : Core.Result.t_Result (t_P256FieldElement & t_P256FieldElement) t_Error =
  if p <>. q
  then point_add_distinct p q
  else Core.Result.Result.v_Ok (jacobian_to_affine (point_double (affine_to_jacobian p)))

let p256_validate_private_key (k: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : bool =
  let valid:bool = true in
  let k_element:t_P256Scalar = from_byte_seq_be_under_impl_68 k in
  let k_element_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    to_byte_seq_be_under_impl_68 k_element
  in
  let all_zero:bool = true in
  let all_zero, valid:(bool & bool) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 k
            }))
      (all_zero, valid)
      (fun (all_zero, valid) i ->
          let all_zero:bool =
            if ~.(Hacspec_lib.Traits.Numeric.equal k.[ i ] (Secret_integers.U8 0uy))
            then
              let all_zero:bool = false in
              all_zero
            else all_zero
          in
          if ~.(Hacspec_lib.Traits.Numeric.equal k_element_bytes.[ i ] k.[ i ])
          then
            let valid:bool = false in
            all_zero, valid
          else all_zero, valid)
  in
  Prims.op_AmpAmp valid ~.all_zero

let p256_validate_public_key (p: (t_P256FieldElement & t_P256FieldElement)) : bool =
  let b:t_P256FieldElement =
    from_byte_seq_be_under_impl_1 (Hacspec_lib.Seq.from_vec_under_impl_52 (Alloc.Slice.into_vec_under_impl
              (Rust_primitives.unsize Rust_primitives.Hax.box_new)))
  in
  let point_at_infinity:bool = is_point_at_infinity (affine_to_jacobian p) in
  let x, y:(t_P256FieldElement & t_P256FieldElement) = p in
  let on_curve:bool =
    y *. y =. x *. x *. x -. from_literal_under_impl_64 (pub_u128 3sz) *. x +. b
  in
  Prims.op_AmpAmp ~.point_at_infinity on_curve

let p256_calculate_w (x: t_P256FieldElement) : t_P256FieldElement =
  let b:t_P256FieldElement =
    from_byte_seq_be_under_impl_1 (Hacspec_lib.Seq.from_vec_under_impl_52 (Alloc.Slice.into_vec_under_impl
              (Rust_primitives.unsize Rust_primitives.Hax.box_new)))
  in
  let exp:t_P256FieldElement =
    from_byte_seq_be_under_impl_1 (Hacspec_lib.Seq.from_vec_under_impl_52 (Alloc.Slice.into_vec_under_impl
              (Rust_primitives.unsize Rust_primitives.Hax.box_new)))
  in
  let z = x *. x *. x -. from_literal_under_impl_64 (pub_u128 3sz) *. x +. b in
  pow_felem_under_impl_58 z exp