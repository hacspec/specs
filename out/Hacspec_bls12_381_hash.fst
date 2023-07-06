module Hacspec_bls12_381_hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_fphash =
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

unfold
type t_fphashcanvas = lseq pub_uint8 512

unfold
type t_arrfp = lseq uint_size 6

let v_B_IN_BYTES: usize = 32sz

let v_S_IN_BYTES: usize = 64sz

let v_L: usize = 64sz

let v_P_1_2_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 936899308823769933uL;
        Secret_integers.U64 2706051889235351147uL;
        Secret_integers.U64 12843041017062132063uL;
        Secret_integers.U64 12941209323636816658uL;
        Secret_integers.U64 1105070755758604287uL;
        Secret_integers.U64 15924587544893707605uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_P_1_4_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 468449654411884966uL;
        Secret_integers.U64 10576397981472451381uL;
        Secret_integers.U64 15644892545385841839uL;
        Secret_integers.U64 15693976698673184137uL;
        Secret_integers.U64 552535377879302143uL;
        Secret_integers.U64 17185665809301629611uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_P_3_4_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 468449654411884966uL;
        Secret_integers.U64 10576397981472451381uL;
        Secret_integers.U64 15644892545385841839uL;
        Secret_integers.U64 15693976698673184137uL;
        Secret_integers.U64 552535377879302143uL;
        Secret_integers.U64 17185665809301629610uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let expand_message_xmd (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (len_in_bytes: usize)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let ell:usize = (len_in_bytes +. v_B_IN_BYTES -. 1sz) /. v_B_IN_BYTES in
  let dst_prime:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.push_under_impl_41 dst
      (Secret_integers.v_U8_from_usize (Hacspec_lib.Seq.len_under_impl_41 dst))
  in
  let z_pad:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 v_S_IN_BYTES
  in
  let l_i_b_str:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 2sz
  in
  let l_i_b_str:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at l_i_b_str
      0l
      (Secret_integers.v_U8_from_usize (len_in_bytes /. 256sz))
  in
  let l_i_b_str:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at l_i_b_str 1l (Secret_integers.v_U8_from_usize len_in_bytes)
  in
  let msg_prime:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_lib.Seq.concat_under_impl_41
              (Hacspec_lib.Seq.concat_under_impl_41 z_pad msg)
              l_i_b_str)
          (Hacspec_lib.Seq.new_under_impl_41 1sz))
      dst_prime
  in
  let b_0:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.from_seq_under_impl_52 (Hacspec_sha256.hash msg_prime)
  in
  let b_i:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.from_seq_under_impl_52 (Hacspec_sha256.hash (Hacspec_lib.Seq.concat_under_impl_41
              (Hacspec_lib.Seq.push_under_impl_41 b_0 (Secret_integers.U8 1uy))
              dst_prime))
  in
  let uniform_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.from_seq_under_impl_52 b_i
  in
  let b_i, uniform_bytes:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 &
    Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 2sz;
              Core.Ops.Range.Range.f_end = ell +. 1sz
            }))
      (b_i, uniform_bytes)
      (fun (b_i, uniform_bytes) i ->
          let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.from_seq_under_impl_52 b_0
          in
          let b_i:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.from_seq_under_impl_52 (Hacspec_sha256.hash (Hacspec_lib.Seq.concat_under_impl_41
                      (Hacspec_lib.Seq.push_under_impl_41 (t ^. b_i)
                          (Secret_integers.v_U8_from_usize i))
                      dst_prime))
          in
          let uniform_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.concat_under_impl_41 uniform_bytes b_i
          in
          b_i, uniform_bytes)
  in
  Hacspec_lib.Seq.truncate_under_impl_41 uniform_bytes len_in_bytes

let fp_hash_to_field (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (count: usize)
    : Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
  let len_in_bytes:usize = count *. v_L in
  let uniform_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    expand_message_xmd msg dst len_in_bytes
  in
  let output:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Hacspec_lib.Seq.new_under_impl_41 count
  in
  let output:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = count
            }))
      output
      (fun output i ->
          let elm_offset:usize = v_L *. i in
          let tv:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.slice_under_impl_41 uniform_bytes elm_offset v_L
          in
          let u_i:Hacspec_bls12_381.t_Fp =
            Hacspec_bls12_381.from_byte_seq_be_under_impl (Hacspec_lib.Seq.slice_under_impl_41 (to_byte_seq_be_under_impl
                      (from_byte_seq_be_under_impl tv))
                  16sz
                  48sz)
          in
          let output:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
            Rust_primitives.Hax.update_at output i u_i
          in
          output)
  in
  output

let fp_sgn0 (x: Hacspec_bls12_381.t_Fp) : bool =
  x %. Hacspec_lib.Traits.Integer.v_TWO =. Hacspec_lib.Traits.Integer.v_ONE

let fp_is_square (x: Hacspec_bls12_381.t_Fp) : bool =
  let c1:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_P_1_2_)
  in
  let tv:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Numeric.pow_self x c1 in
  Prims.op_BarBar (tv =. Hacspec_lib.Traits.Integer.v_ZERO) (tv =. Hacspec_lib.Traits.Integer.v_ONE)

let fp_sqrt (x: Hacspec_bls12_381.t_Fp) : Hacspec_bls12_381.t_Fp =
  let c1:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_P_1_4_)
  in
  Hacspec_lib.Traits.Numeric.pow_self x c1

let g1_curve_func (x: Hacspec_bls12_381.t_Fp) : _ =
  x *. x *. x +. Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 4sz)

let g1_map_to_curve_svdw (u: Hacspec_bls12_381.t_Fp)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let z =
    Hacspec_lib.Traits.Integer.v_ZERO -. Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 3sz)
  in
  let gz:Hacspec_bls12_381.t_Fp = g1_curve_func z in
  let tv1 = u *. u *. gz in
  let tv2 = Hacspec_lib.Traits.Integer.v_ONE +. tv1 in
  let tv1 = Hacspec_lib.Traits.Integer.v_ONE -. tv1 in
  let tv3:Hacspec_bls12_381.t_Fp = Hacspec_bls12_381.inv_under_impl_57 (tv1 *. tv2) in
  let tv4:Hacspec_bls12_381.t_Fp =
    fp_sqrt ((Hacspec_lib.Traits.Integer.v_ZERO -. gz) *.
        (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 3sz) *. z *. z))
  in
  let tv4 =
    if fp_sgn0 tv4
    then
      let tv4 = Hacspec_lib.Traits.Integer.v_ZERO -. tv4 in
      tv4
    else tv4
  in
  let tv5 = u *. tv1 *. tv3 *. tv4 in
  let tv6 =
    (Hacspec_lib.Traits.Integer.v_ZERO -.
      Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 4sz)) *.
    gz *.
    Hacspec_bls12_381.inv_under_impl_57 (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 3sz) *.
        z *.
        z)
  in
  let x1 =
    (Hacspec_lib.Traits.Integer.v_ZERO -. z) *.
    Hacspec_bls12_381.inv_under_impl_57 Hacspec_lib.Traits.Integer.v_TWO -.
    tv5
  in
  let x2 =
    (Hacspec_lib.Traits.Integer.v_ZERO -. z) *.
    Hacspec_bls12_381.inv_under_impl_57 Hacspec_lib.Traits.Integer.v_TWO +.
    tv5
  in
  let x3 = z +. tv6 *. (tv2 *. tv2 *. tv3) *. (tv2 *. tv2 *. tv3) in
  let x:Hacspec_bls12_381.t_Fp =
    if fp_is_square (g1_curve_func x1)
    then x1
    else if fp_is_square (g1_curve_func x2) then x2 else x3
  in
  let y:Hacspec_bls12_381.t_Fp = fp_sqrt (g1_curve_func x) in
  let y =
    if fp_sgn0 u <>. fp_sgn0 y
    then
      let y = Hacspec_lib.Traits.Integer.v_ZERO -. y in
      y
    else y
  in
  x, y, false

let g1_clear_cofactor (x: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool))
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let h_eff:Hacspec_bls12_381.t_Scalar =
    Hacspec_bls12_381.from_literal_under_impl_199 (pub_u128 15132376222941642753sz)
  in
  Hacspec_bls12_381.g1mul h_eff x

let g1_hash_to_curve_svdw (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let u:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp = fp_hash_to_field msg dst 2sz in
  let q0:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = g1_map_to_curve_svdw u.[ 0l ] in
  let q1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = g1_map_to_curve_svdw u.[ 1l ] in
  let r:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = Hacspec_bls12_381.g1add q0 q1 in
  g1_clear_cofactor r

let g1_encode_to_curve_svdw (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let u:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp = fp_hash_to_field msg dst 1sz in
  let q:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = g1_map_to_curve_svdw u.[ 0l ] in
  g1_clear_cofactor q

let fp2_hash_to_field (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (count: usize)
    : Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
  let len_in_bytes:usize = count *. 2sz *. v_L in
  let uniform_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    expand_message_xmd msg dst len_in_bytes
  in
  let output:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Seq.new_under_impl_41 count
  in
  let output:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = count
            }))
      output
      (fun output i ->
          let elm_offset:usize = v_L *. i *. 2sz in
          let tv:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.slice_under_impl_41 uniform_bytes elm_offset v_L
          in
          let e_1:Hacspec_bls12_381.t_Fp =
            Hacspec_bls12_381.from_byte_seq_be_under_impl (Hacspec_lib.Seq.slice_under_impl_41 (to_byte_seq_be_under_impl
                      (from_byte_seq_be_under_impl tv))
                  16sz
                  48sz)
          in
          let elm_offset:usize = v_L *. (1sz +. i *. 2sz) in
          let tv:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.slice_under_impl_41 uniform_bytes elm_offset v_L
          in
          let e_2:Hacspec_bls12_381.t_Fp =
            Hacspec_bls12_381.from_byte_seq_be_under_impl (Hacspec_lib.Seq.slice_under_impl_41 (to_byte_seq_be_under_impl
                      (from_byte_seq_be_under_impl tv))
                  16sz
                  48sz)
          in
          let output:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Rust_primitives.Hax.update_at output i (e_1, e_2)
          in
          output)
  in
  output

let fp2_sgn0 (x: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) : bool =
  let x0, x1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = x in
  let sign_0:bool = fp_sgn0 x0 in
  let zero_0:bool = x0 =. Hacspec_lib.Traits.Integer.v_ZERO in
  let sign_1:bool = fp_sgn0 x1 in
  Prims.op_BarBar sign_0 (Prims.op_AmpAmp zero_0 sign_1)

let fp2_is_square (x: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) : bool =
  let c1:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_P_1_2_)
  in
  let x1, x2:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = x in
  let tv1 = x1 *. x1 in
  let tv2 = x2 *. x2 in
  let tv1 = tv1 +. tv2 in
  let tv1:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Numeric.pow_self tv1 c1 in
  let neg1 = Hacspec_lib.Traits.Integer.v_ZERO -. Hacspec_lib.Traits.Integer.v_ONE in
  tv1 <>. neg1

let fp2exp (n: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) (k: Hacspec_bls12_381.t_Fp)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
  let c:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE
  in
  let c:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 381sz
            }))
      c
      (fun c i ->
          let c:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2mul c c in
          if Hacspec_bls12_381.bit_under_impl_63 k (380sz -. i)
          then
            let c:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
              Hacspec_bls12_381.fp2mul c n
            in
            c
          else c)
  in
  c

let fp2_sqrt (a: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp))
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
  let c1:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_P_3_4_)
  in
  let c2:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_P_1_2_)
  in
  let a1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = fp2exp a c1 in
  let alpha:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul a1 (Hacspec_bls12_381.fp2mul a1 a)
  in
  let x0:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2mul a1 a in
  let neg1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Traits.Integer.v_ZERO -. Hacspec_lib.Traits.Integer.v_ONE,
    Hacspec_lib.Traits.Integer.v_ZERO
  in
  let b:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    fp2exp (Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE)
          alpha)
      c2
  in
  if alpha =. neg1
  then
    Hacspec_bls12_381.fp2mul (Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ONE)
      x0
  else Hacspec_bls12_381.fp2mul b x0

let g2_curve_func (x: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp))
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
  Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2mul x (Hacspec_bls12_381.fp2mul x x))
    (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 4sz),
      Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 4sz))

let g2_map_to_curve_svdw (u: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp))
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let z:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2neg (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE)
  in
  let gz:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = g2_curve_func z in
  let tv1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul u u) gz
  in
  let tv2:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE) tv1
  in
  let tv1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2sub (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE) tv1
  in
  let tv3:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2inv (Hacspec_bls12_381.fp2mul tv1 tv2)
  in
  let tv4:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    fp2_sqrt (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2neg gz)
          (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2fromfp (Hacspec_bls12_381.from_literal_under_impl_63
                      (pub_u128 3sz)))
              (Hacspec_bls12_381.fp2mul z z)))
  in
  let tv4:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    if fp2_sgn0 tv4
    then
      let tv4:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2neg tv4 in
      tv4
    else tv4
  in
  let tv5:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul u tv1) tv3) tv4
  in
  let tv6:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2neg (Hacspec_bls12_381.fp2fromfp
                  (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 4sz))))
          gz)
      (Hacspec_bls12_381.fp2inv (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2fromfp (Hacspec_bls12_381.from_literal_under_impl_63
                      (pub_u128 3sz)))
              (Hacspec_bls12_381.fp2mul z z)))
  in
  let x1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2sub (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2neg z)
          (Hacspec_bls12_381.fp2inv (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_TWO)))
      tv5
  in
  let x2:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2neg z)
          (Hacspec_bls12_381.fp2inv (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_TWO)))
      tv5
  in
  let tv7:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul tv2 tv2) tv3
  in
  let x3:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2add z (Hacspec_bls12_381.fp2mul tv6 (Hacspec_bls12_381.fp2mul tv7 tv7))
  in
  let x:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    if fp2_is_square (g2_curve_func x1)
    then x1
    else if fp2_is_square (g2_curve_func x2) then x2 else x3
  in
  let y:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = fp2_sqrt (g2_curve_func x) in
  let y:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    if fp2_sgn0 u <>. fp2_sgn0 y
    then
      let y:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2neg y in
      y
    else y
  in
  x, y, false

let psi
      (p:
          ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
            (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
            bool))
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let c1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2inv (fp2exp (Hacspec_lib.Traits.Integer.v_ONE,
            Hacspec_lib.Traits.Integer.v_ONE)
          ((Hacspec_lib.Traits.Integer.v_ZERO -. Hacspec_lib.Traits.Integer.v_ONE) *.
            Hacspec_bls12_381.inv_under_impl_57 (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128
                    3sz))))
  in
  let c2:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2inv (fp2exp (Hacspec_lib.Traits.Integer.v_ONE,
            Hacspec_lib.Traits.Integer.v_ONE)
          ((Hacspec_lib.Traits.Integer.v_ZERO -. Hacspec_lib.Traits.Integer.v_ONE) *.
            Hacspec_bls12_381.inv_under_impl_57 Hacspec_lib.Traits.Integer.v_TWO))
  in
  let x, y, inf:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    p
  in
  let qx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul c1 (Hacspec_bls12_381.fp2conjugate x)
  in
  let qy:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul c2 (Hacspec_bls12_381.fp2conjugate y)
  in
  qx, qy, inf

let g2_clear_cofactor
      (p:
          ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
            (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
            bool))
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let c1:Hacspec_bls12_381.t_Scalar =
    Hacspec_bls12_381.from_literal_under_impl_199 (pub_u128 15132376222941642752sz)
  in
  let t1:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2mul c1 p
  in
  let t1:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2neg t1
  in
  let t2:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    psi p
  in
  let t3:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2double p
  in
  let t3:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    psi (psi t3)
  in
  let t3:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2add t3 (Hacspec_bls12_381.g2neg t2)
  in
  let t2:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2add t1 t2
  in
  let t2:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2mul c1 t2
  in
  let t2:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2neg t2
  in
  let t3:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2add t3 t2
  in
  let t3:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2add t3 (Hacspec_bls12_381.g2neg t1)
  in
  Hacspec_bls12_381.g2add t3 (Hacspec_bls12_381.g2neg p)

let g2_hash_to_curve_svdw (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let u:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    fp2_hash_to_field msg dst 2sz
  in
  let q0:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    g2_map_to_curve_svdw u.[ 0l ]
  in
  let q1:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    g2_map_to_curve_svdw u.[ 1l ]
  in
  let r:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2add q0 q1
  in
  g2_clear_cofactor r

let g2_encode_to_curve_svdw (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let u:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    fp2_hash_to_field msg dst 1sz
  in
  let q:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    g2_map_to_curve_svdw u.[ 0l ]
  in
  g2_clear_cofactor q

let v_G1_ISO_A: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 5707120929990979uL;
        Secret_integers.U64 4425131892511951234uL;
        Secret_integers.U64 12748169179688756904uL;
        Secret_integers.U64 15629909748249821612uL;
        Secret_integers.U64 10994253769421683071uL;
        Secret_integers.U64 6698022561392380957uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_ISO_B: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1360808972976160816uL;
        Secret_integers.U64 111203405409480251uL;
        Secret_integers.U64 2312248699302920304uL;
        Secret_integers.U64 11581500465278574325uL;
        Secret_integers.U64 6495071758858381989uL;
        Secret_integers.U64 15117538217124375520uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1270119733718627136uL;
        Secret_integers.U64 13261148298159854981uL;
        Secret_integers.U64 7723742117508874335uL;
        Secret_integers.U64 17465657917644792520uL;
        Secret_integers.U64 6201670911048166766uL;
        Secret_integers.U64 12586459670690286007uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_1_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1668951808976071471uL;
        Secret_integers.U64 398773841247578140uL;
        Secret_integers.U64 8941869963990959127uL;
        Secret_integers.U64 17682789360670468203uL;
        Secret_integers.U64 5204176168283587414uL;
        Secret_integers.U64 16732261237459223483uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_2_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 960393023080265964uL;
        Secret_integers.U64 2094253841180170779uL;
        Secret_integers.U64 14844748873776858085uL;
        Secret_integers.U64 7528018573573808732uL;
        Secret_integers.U64 10776056440809943711uL;
        Secret_integers.U64 16147550488514976944uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_3_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1691355743628586423uL;
        Secret_integers.U64 5622191986793862162uL;
        Secret_integers.U64 15561595211679121189uL;
        Secret_integers.U64 17416319752018800771uL;
        Secret_integers.U64 5996228842464768403uL;
        Secret_integers.U64 14245880009877842017uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_4_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1051997788391994435uL;
        Secret_integers.U64 7368650625050054228uL;
        Secret_integers.U64 11086623519836470079uL;
        Secret_integers.U64 607681821319080984uL;
        Secret_integers.U64 10978131499682789316uL;
        Secret_integers.U64 5842660658088809945uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_5_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1598992431623377919uL;
        Secret_integers.U64 130921168661596853uL;
        Secret_integers.U64 15797696746983946651uL;
        Secret_integers.U64 11444679715590672272uL;
        Secret_integers.U64 11567228658253249817uL;
        Secret_integers.U64 14777367860349315459uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_6_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 967946631563726121uL;
        Secret_integers.U64 7653628713030275775uL;
        Secret_integers.U64 12760252618317466849uL;
        Secret_integers.U64 10378793938173061930uL;
        Secret_integers.U64 10205808941053849290uL;
        Secret_integers.U64 15985511645807504772uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_7_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1709149555065084898uL;
        Secret_integers.U64 16750075057192140371uL;
        Secret_integers.U64 3849985779734105521uL;
        Secret_integers.U64 11998370262181639475uL;
        Secret_integers.U64 4159013751748851119uL;
        Secret_integers.U64 11298218755092433038uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_8_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 580186936973955012uL;
        Secret_integers.U64 8903813505199544589uL;
        Secret_integers.U64 14140024565662700916uL;
        Secret_integers.U64 11728946595272970718uL;
        Secret_integers.U64 5738313744366653077uL;
        Secret_integers.U64 7886252005760951063uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_9_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1628930385436977092uL;
        Secret_integers.U64 3318087848058654498uL;
        Secret_integers.U64 15937899882900905113uL;
        Secret_integers.U64 7449821001803307903uL;
        Secret_integers.U64 11752436998487615353uL;
        Secret_integers.U64 9161465579737517214uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_10_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1167027828517898210uL;
        Secret_integers.U64 8275623842221021965uL;
        Secret_integers.U64 18049808134997311382uL;
        Secret_integers.U64 15351349873550116966uL;
        Secret_integers.U64 17769927732099571180uL;
        Secret_integers.U64 14584871380308065147uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XNUM_K_11_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 495550047642324592uL;
        Secret_integers.U64 13627494601717575229uL;
        Secret_integers.U64 3591512392926246844uL;
        Secret_integers.U64 2576269112800734056uL;
        Secret_integers.U64 14000314106239596831uL;
        Secret_integers.U64 12234233096825917993uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 633474091881273774uL;
        Secret_integers.U64 1779737893574802031uL;
        Secret_integers.U64 132274872219551930uL;
        Secret_integers.U64 11283074393783708770uL;
        Secret_integers.U64 13067430171545714168uL;
        Secret_integers.U64 11041975239630265116uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_1_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1321272531362356291uL;
        Secret_integers.U64 5238936591227237942uL;
        Secret_integers.U64 8089002360232247308uL;
        Secret_integers.U64 82967328719421271uL;
        Secret_integers.U64 1430641118356186857uL;
        Secret_integers.U64 16557527386785790975uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_2_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 804282852993868382uL;
        Secret_integers.U64 9311163821600184607uL;
        Secret_integers.U64 8037026956533927121uL;
        Secret_integers.U64 18205324308570099372uL;
        Secret_integers.U64 15466434890074226396uL;
        Secret_integers.U64 18213183315621985817uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_3_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 234844145893171966uL;
        Secret_integers.U64 14428037799351479124uL;
        Secret_integers.U64 6559532710647391569uL;
        Secret_integers.U64 6110444250091843536uL;
        Secret_integers.U64 5293652763671852484uL;
        Secret_integers.U64 1373009181854280920uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_4_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1416629893867312296uL;
        Secret_integers.U64 751851957792514173uL;
        Secret_integers.U64 18437674587247370939uL;
        Secret_integers.U64 10190314345946351322uL;
        Secret_integers.U64 11228207967368476701uL;
        Secret_integers.U64 6025034940388909598uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_5_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1041270466333271993uL;
        Secret_integers.U64 6140956605115975401uL;
        Secret_integers.U64 4131830461445745997uL;
        Secret_integers.U64 739642499118176303uL;
        Secret_integers.U64 8358912131254619921uL;
        Secret_integers.U64 13847998906088228005uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_6_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 536714149743900185uL;
        Secret_integers.U64 1098328982230230817uL;
        Secret_integers.U64 6273329123533496713uL;
        Secret_integers.U64 5633448088282521244uL;
        Secret_integers.U64 16894043798660571244uL;
        Secret_integers.U64 17016134625831438906uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_7_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1488347500898461874uL;
        Secret_integers.U64 3509418672874520985uL;
        Secret_integers.U64 7962192351555381416uL;
        Secret_integers.U64 1843909372225399896uL;
        Secret_integers.U64 1127511003250156243uL;
        Secret_integers.U64 1294742680819751518uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_8_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 725340084226051970uL;
        Secret_integers.U64 6814521545734988748uL;
        Secret_integers.U64 16176803544133875307uL;
        Secret_integers.U64 8363199516777220149uL;
        Secret_integers.U64 252877309218538352uL;
        Secret_integers.U64 5149562959837648449uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_XDEN_K_9_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 675470927100193492uL;
        Secret_integers.U64 5146891164735334016uL;
        Secret_integers.U64 17762958817130696759uL;
        Secret_integers.U64 8565656522589412373uL;
        Secret_integers.U64 10599026333335446784uL;
        Secret_integers.U64 3270603789344496906uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 652344406751465184uL;
        Secret_integers.U64 2710356675495255290uL;
        Secret_integers.U64 1273695771440998738uL;
        Secret_integers.U64 3121750372618945491uL;
        Secret_integers.U64 14775319642720936898uL;
        Secret_integers.U64 13733803417833814835uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_1_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1389807578337138705uL;
        Secret_integers.U64 15352831428748068483uL;
        Secret_integers.U64 1307144967559264317uL;
        Secret_integers.U64 1121505450578652468uL;
        Secret_integers.U64 15475889019760388287uL;
        Secret_integers.U64 16183658160488302230uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_2_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 57553299067792998uL;
        Secret_integers.U64 17628079362768849300uL;
        Secret_integers.U64 2689461337731570914uL;
        Secret_integers.U64 14070580367580990887uL;
        Secret_integers.U64 15162865775551710499uL;
        Secret_integers.U64 13321614990632673782uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_3_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 141972750621744161uL;
        Secret_integers.U64 8689824239172478807uL;
        Secret_integers.U64 15288216298323671324uL;
        Secret_integers.U64 712874875091754233uL;
        Secret_integers.U64 16014900032503684588uL;
        Secret_integers.U64 11976580453200426187uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_4_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 633886036738506515uL;
        Secret_integers.U64 6678644607214234052uL;
        Secret_integers.U64 1825425679455244472uL;
        Secret_integers.U64 8755912272271186652uL;
        Secret_integers.U64 3379943669301788840uL;
        Secret_integers.U64 4735212769449148123uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_5_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1612358804494830442uL;
        Secret_integers.U64 2454990789666711200uL;
        Secret_integers.U64 8405916841409361853uL;
        Secret_integers.U64 8525415512662168654uL;
        Secret_integers.U64 2323684950984523890uL;
        Secret_integers.U64 11074978966450447856uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_6_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 336375361001233340uL;
        Secret_integers.U64 12882959944969186108uL;
        Secret_integers.U64 16671121624101127371uL;
        Secret_integers.U64 5922586712221110071uL;
        Secret_integers.U64 5163511947597922654uL;
        Secret_integers.U64 14511152726087948018uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_7_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 686738286210365551uL;
        Secret_integers.U64 16039894141796533876uL;
        Secret_integers.U64 1660145734357211167uL;
        Secret_integers.U64 18231571463891878950uL;
        Secret_integers.U64 4825120264949852469uL;
        Secret_integers.U64 11627815551290637097uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_8_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 719520515476580427uL;
        Secret_integers.U64 16756942182913253819uL;
        Secret_integers.U64 10320769399998235244uL;
        Secret_integers.U64 2200974244968450750uL;
        Secret_integers.U64 7626373186594408355uL;
        Secret_integers.U64 6933025920263103879uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_9_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1016611174344998325uL;
        Secret_integers.U64 2466492548686891555uL;
        Secret_integers.U64 14135124294293452542uL;
        Secret_integers.U64 475233659467912251uL;
        Secret_integers.U64 11186783513499056751uL;
        Secret_integers.U64 3147922594245844016uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_10_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1833315000454533566uL;
        Secret_integers.U64 1007974600900082579uL;
        Secret_integers.U64 14785260176242854207uL;
        Secret_integers.U64 15066861003931772432uL;
        Secret_integers.U64 3584647998681889532uL;
        Secret_integers.U64 16722834201330696498uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_11_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1780164921828767454uL;
        Secret_integers.U64 13337622794239929804uL;
        Secret_integers.U64 5923739534552515142uL;
        Secret_integers.U64 3345046972101780530uL;
        Secret_integers.U64 5321510883028162054uL;
        Secret_integers.U64 14846055306840460686uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_12_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 799438051374502809uL;
        Secret_integers.U64 15083972834952036164uL;
        Secret_integers.U64 8838227588559581326uL;
        Secret_integers.U64 13846054168121598783uL;
        Secret_integers.U64 488730451382505970uL;
        Secret_integers.U64 958146249756188408uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_13_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 163716820423854747uL;
        Secret_integers.U64 8285498163857659356uL;
        Secret_integers.U64 8465424830341846400uL;
        Secret_integers.U64 1433942577299613084uL;
        Secret_integers.U64 14325828012864645732uL;
        Secret_integers.U64 4817114329354076467uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_14_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 414658151749832465uL;
        Secret_integers.U64 189531577938912252uL;
        Secret_integers.U64 6802473390048830824uL;
        Secret_integers.U64 15684647020317539556uL;
        Secret_integers.U64 7755485098777620407uL;
        Secret_integers.U64 9685868895687483979uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YNUM_K_15_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1578157964224562126uL;
        Secret_integers.U64 5666948055268535989uL;
        Secret_integers.U64 14634479491382401593uL;
        Secret_integers.U64 6317940024988860850uL;
        Secret_integers.U64 13142913832013798519uL;
        Secret_integers.U64 338991247778166276uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1590100849350973618uL;
        Secret_integers.U64 5915497081334721257uL;
        Secret_integers.U64 6924968209373727718uL;
        Secret_integers.U64 17204633670617869946uL;
        Secret_integers.U64 572916540828819565uL;
        Secret_integers.U64 92203205520679873uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_1_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1829261189398470686uL;
        Secret_integers.U64 1877083417397643448uL;
        Secret_integers.U64 9640042925497046428uL;
        Secret_integers.U64 11862766565471805471uL;
        Secret_integers.U64 8693114993904885301uL;
        Secret_integers.U64 3672140328108400701uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_2_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 400243331105348135uL;
        Secret_integers.U64 8046435537999802711uL;
        Secret_integers.U64 8702226981475745585uL;
        Secret_integers.U64 879791671491744492uL;
        Secret_integers.U64 11994630442058346377uL;
        Secret_integers.U64 2172204746352322546uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_3_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1637008473169220501uL;
        Secret_integers.U64 17441636237435581649uL;
        Secret_integers.U64 15066165676546511630uL;
        Secret_integers.U64 1314387578457599809uL;
        Secret_integers.U64 8247046336453711789uL;
        Secret_integers.U64 12164906044230685718uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_4_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 855930740911588324uL;
        Secret_integers.U64 12685735333705453020uL;
        Secret_integers.U64 14326404096614579120uL;
        Secret_integers.U64 6066025509460822294uL;
        Secret_integers.U64 11676450493790612973uL;
        Secret_integers.U64 15724621714793234461uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_5_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 637792788410719021uL;
        Secret_integers.U64 11507373155986977154uL;
        Secret_integers.U64 13186912195705886849uL;
        Secret_integers.U64 14262012144631372388uL;
        Secret_integers.U64 5328758613570342114uL;
        Secret_integers.U64 199925847119476652uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_6_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1612297190139091759uL;
        Secret_integers.U64 14103733843373163083uL;
        Secret_integers.U64 6840121186619029743uL;
        Secret_integers.U64 6760859324815900753uL;
        Secret_integers.U64 15418807805142572985uL;
        Secret_integers.U64 4402853133867972444uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_7_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1631410310868805610uL;
        Secret_integers.U64 269334146695233390uL;
        Secret_integers.U64 16547411811928854487uL;
        Secret_integers.U64 18353100669930795314uL;
        Secret_integers.U64 13339932232668798692uL;
        Secret_integers.U64 6984591927261867737uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_8_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1758313625630302499uL;
        Secret_integers.U64 1881349400343039172uL;
        Secret_integers.U64 18013005311323887904uL;
        Secret_integers.U64 12377427846571989832uL;
        Secret_integers.U64 5967237584920922243uL;
        Secret_integers.U64 7720081932193848650uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_9_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1619701357752249884uL;
        Secret_integers.U64 16898074901591262352uL;
        Secret_integers.U64 3609344159736760251uL;
        Secret_integers.U64 5983130161189999867uL;
        Secret_integers.U64 14355327869992416094uL;
        Secret_integers.U64 3778226018344582997uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_10_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 347606589330687421uL;
        Secret_integers.U64 5255719044972187933uL;
        Secret_integers.U64 11271894388753671721uL;
        Secret_integers.U64 1033887512062764488uL;
        Secret_integers.U64 8189165486932690436uL;
        Secret_integers.U64 70004379462101672uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_11_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 778202887894139711uL;
        Secret_integers.U64 17691595219776375879uL;
        Secret_integers.U64 9193253711563866834uL;
        Secret_integers.U64 10092455202333888821uL;
        Secret_integers.U64 1655469341950262250uL;
        Secret_integers.U64 10845992994110574738uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_12_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 781015344221683683uL;
        Secret_integers.U64 14078588081290548374uL;
        Secret_integers.U64 6067271023149908518uL;
        Secret_integers.U64 9033357708497886086uL;
        Secret_integers.U64 10592474449179118273uL;
        Secret_integers.U64 2204988348113831372uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_13_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 172830037692534587uL;
        Secret_integers.U64 7101012286790006514uL;
        Secret_integers.U64 13787308004332873665uL;
        Secret_integers.U64 14660498759553796110uL;
        Secret_integers.U64 4757234684169342080uL;
        Secret_integers.U64 15130647872920159991uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G1_YDEN_K_14_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1013206390650290238uL;
        Secret_integers.U64 7720336747103001025uL;
        Secret_integers.U64 8197694151986493523uL;
        Secret_integers.U64 3625112747029342752uL;
        Secret_integers.U64 6675167463148394368uL;
        Secret_integers.U64 4905905684016745359uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let g1_simple_swu_iso (u: Hacspec_bls12_381.t_Fp)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
  let z:Hacspec_bls12_381.t_Fp = Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 11sz) in
  let a:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_ISO_A)
  in
  let b:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_ISO_B)
  in
  let tv1:Hacspec_bls12_381.t_Fp =
    Hacspec_bls12_381.inv_under_impl_57 (z *. z *. Hacspec_lib.Traits.Numeric.exp u 4ul +.
        z *. u *. u)
  in
  let x1 =
    (Hacspec_lib.Traits.Integer.v_ZERO -. b) *. Hacspec_bls12_381.inv_under_impl_57 a *.
    (Hacspec_lib.Traits.Integer.v_ONE +. tv1)
  in
  let x1 =
    if tv1 =. Hacspec_lib.Traits.Integer.v_ZERO
    then
      let x1 = b *. Hacspec_bls12_381.inv_under_impl_57 (z *. a) in
      x1
    else x1
  in
  let gx1 = Hacspec_lib.Traits.Numeric.exp x1 3ul +. a *. x1 +. b in
  let x2 = z *. u *. u *. x1 in
  let gx2 = Hacspec_lib.Traits.Numeric.exp x2 3ul +. a *. x2 +. b in
  let x, y:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    if fp_is_square gx1 then x1, fp_sqrt gx1 else x2, fp_sqrt gx2
  in
  let y =
    if fp_sgn0 u <>. fp_sgn0 y
    then
      let y = Hacspec_lib.Traits.Integer.v_ZERO -. y in
      y
    else y
  in
  x, y

let g1_isogeny_map (x y: Hacspec_bls12_381.t_Fp)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Hacspec_lib.Seq.new_under_impl_41 12sz
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_0_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      1sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_1_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      2sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_2_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      3sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_3_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      4sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_4_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      5sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_5_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      6sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_6_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      7sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_7_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      8sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_8_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      9sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_9_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      10sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_10_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xnum_k
      11sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XNUM_K_11_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Hacspec_lib.Seq.new_under_impl_41 10sz
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_0_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      1sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_1_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      2sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_2_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      3sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_3_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      4sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_4_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      5sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_5_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      6sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_6_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      7sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_7_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      8sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_8_))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at xden_k
      9sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_XDEN_K_9_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Hacspec_lib.Seq.new_under_impl_41 16sz
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_0_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      1sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_1_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      2sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_2_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      3sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_3_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      4sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_4_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      5sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_5_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      6sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_6_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      7sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_7_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      8sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_8_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      9sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_9_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      10sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_10_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      11sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_11_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      12sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_12_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      13sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_13_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      14sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_14_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at ynum_k
      15sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YNUM_K_15_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Hacspec_lib.Seq.new_under_impl_41 15sz
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_0_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      1sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_1_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      2sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_2_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      3sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_3_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      4sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_4_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      5sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_5_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      6sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_6_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      7sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_7_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      8sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_8_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      9sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_9_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      10sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_10_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      11sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_11_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      12sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_12_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      13sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_13_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp =
    Rust_primitives.Hax.update_at yden_k
      14sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G1_YDEN_K_14_))
  in
  let xnum:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ZERO in
  let xx:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ONE in
  let xnum, xx:(_ & _) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 xnum_k
            }))
      (xnum, xx)
      (fun (xnum, xx) i ->
          let xnum = xnum +. xx *. xnum_k.[ i ] in
          let xx = xx *. x in
          xnum, xx)
  in
  let xden:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ZERO in
  let xx:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ONE in
  let xden, xx:(_ & _) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 xden_k
            }))
      (xden, xx)
      (fun (xden, xx) i ->
          let xden = xden +. xx *. xden_k.[ i ] in
          let xx = xx *. x in
          xden, xx)
  in
  let xden = xden +. xx in
  let ynum:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ZERO in
  let xx:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ONE in
  let xx, ynum:(_ & _) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 ynum_k
            }))
      (xx, ynum)
      (fun (xx, ynum) i ->
          let ynum = ynum +. xx *. ynum_k.[ i ] in
          let xx = xx *. x in
          xx, ynum)
  in
  let yden:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ZERO in
  let xx:Hacspec_bls12_381.t_Fp = Hacspec_lib.Traits.Integer.v_ONE in
  let xx, yden:(_ & _) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 yden_k
            }))
      (xx, yden)
      (fun (xx, yden) i ->
          let yden = yden +. xx *. yden_k.[ i ] in
          let xx = xx *. x in
          xx, yden)
  in
  let yden = yden +. xx in
  let xr = xnum *. Hacspec_bls12_381.inv_under_impl_57 xden in
  let yr = y *. ynum *. Hacspec_bls12_381.inv_under_impl_57 yden in
  let inf:bool = false in
  let inf:bool =
    if
      Prims.op_BarBar (xden =. Hacspec_lib.Traits.Integer.v_ZERO)
        (yden =. Hacspec_lib.Traits.Integer.v_ZERO)
    then
      let inf:bool = true in
      inf
    else inf
  in
  xr, yr, inf

let g1_map_to_curve_sswu (u: Hacspec_bls12_381.t_Fp)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let xp, yp:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = g1_simple_swu_iso u in
  g1_isogeny_map xp yp

let g1_hash_to_curve_sswu (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let u:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp = fp_hash_to_field msg dst 2sz in
  let q0:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = g1_map_to_curve_sswu u.[ 0l ] in
  let q1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = g1_map_to_curve_sswu u.[ 1l ] in
  let r:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = Hacspec_bls12_381.g1add q0 q1 in
  g1_clear_cofactor r

let g1_encode_to_curve_sswu (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) =
  let u:Hacspec_lib.Seq.t_Seq Hacspec_bls12_381.t_Fp = fp_hash_to_field msg dst 1sz in
  let q:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp & bool) = g1_map_to_curve_sswu u.[ 0l ] in
  g1_clear_cofactor q

let v_G2_XNUM_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 416399692810564414uL;
        Secret_integers.U64 13500519111022079365uL;
        Secret_integers.U64 3658379999393219626uL;
        Secret_integers.U64 9850925049107374429uL;
        Secret_integers.U64 6640057249351452444uL;
        Secret_integers.U64 7077594464397203414uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_XNUM_K_1_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1249199078431693244uL;
        Secret_integers.U64 3608069185647134863uL;
        Secret_integers.U64 10975139998179658879uL;
        Secret_integers.U64 11106031073612571672uL;
        Secret_integers.U64 1473427674344805717uL;
        Secret_integers.U64 2786039319482058522uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_XNUM_K_2_R: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1249199078431693244uL;
        Secret_integers.U64 3608069185647134863uL;
        Secret_integers.U64 10975139998179658879uL;
        Secret_integers.U64 11106031073612571672uL;
        Secret_integers.U64 1473427674344805717uL;
        Secret_integers.U64 2786039319482058526uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_XNUM_K_2_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 624599539215846622uL;
        Secret_integers.U64 1804034592823567431uL;
        Secret_integers.U64 14710942035944605247uL;
        Secret_integers.U64 14776387573661061644uL;
        Secret_integers.U64 736713837172402858uL;
        Secret_integers.U64 10616391696595805069uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_XNUM_K_3_R: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1665598771242257658uL;
        Secret_integers.U64 17108588296669214228uL;
        Secret_integers.U64 14633519997572878506uL;
        Secret_integers.U64 2510212049010394485uL;
        Secret_integers.U64 8113484923696258161uL;
        Secret_integers.U64 9863633783879261905uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_XDEN_K_0_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1873798617647539866uL;
        Secret_integers.U64 5412103778470702295uL;
        Secret_integers.U64 7239337960414712511uL;
        Secret_integers.U64 7435674573564081700uL;
        Secret_integers.U64 2210141511517208575uL;
        Secret_integers.U64 13402431016077863523uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_XDEN_K_1_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1873798617647539866uL;
        Secret_integers.U64 5412103778470702295uL;
        Secret_integers.U64 7239337960414712511uL;
        Secret_integers.U64 7435674573564081700uL;
        Secret_integers.U64 2210141511517208575uL;
        Secret_integers.U64 13402431016077863583uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YNUM_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1526798873638736187uL;
        Secret_integers.U64 6459500568425337235uL;
        Secret_integers.U64 1116230615302104219uL;
        Secret_integers.U64 17673314439684154624uL;
        Secret_integers.U64 18197961889718808424uL;
        Secret_integers.U64 1355520937843676934uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YNUM_K_1_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 416399692810564414uL;
        Secret_integers.U64 13500519111022079365uL;
        Secret_integers.U64 3658379999393219626uL;
        Secret_integers.U64 9850925049107374429uL;
        Secret_integers.U64 6640057249351452444uL;
        Secret_integers.U64 7077594464397203390uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YNUM_K_2_R: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1249199078431693244uL;
        Secret_integers.U64 3608069185647134863uL;
        Secret_integers.U64 10975139998179658879uL;
        Secret_integers.U64 11106031073612571672uL;
        Secret_integers.U64 1473427674344805717uL;
        Secret_integers.U64 2786039319482058524uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YNUM_K_2_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 624599539215846622uL;
        Secret_integers.U64 1804034592823567431uL;
        Secret_integers.U64 14710942035944605247uL;
        Secret_integers.U64 14776387573661061644uL;
        Secret_integers.U64 736713837172402858uL;
        Secret_integers.U64 10616391696595805071uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YNUM_K_3_R: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1318599027233453979uL;
        Secret_integers.U64 18155985086623849168uL;
        Secret_integers.U64 8510412652460270214uL;
        Secret_integers.U64 12747851915130467410uL;
        Secret_integers.U64 5654561228188306393uL;
        Secret_integers.U64 16263467779354626832uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YDEN_K_0_: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1873798617647539866uL;
        Secret_integers.U64 5412103778470702295uL;
        Secret_integers.U64 7239337960414712511uL;
        Secret_integers.U64 7435674573564081700uL;
        Secret_integers.U64 2210141511517208575uL;
        Secret_integers.U64 13402431016077863163uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YDEN_K_1_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1873798617647539866uL;
        Secret_integers.U64 5412103778470702295uL;
        Secret_integers.U64 7239337960414712511uL;
        Secret_integers.U64 7435674573564081700uL;
        Secret_integers.U64 2210141511517208575uL;
        Secret_integers.U64 13402431016077863379uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let v_G2_YDEN_K_2_I: t_ArrFp =
  ArrFp
  (let l =
      [
        Secret_integers.U64 1873798617647539866uL;
        Secret_integers.U64 5412103778470702295uL;
        Secret_integers.U64 7239337960414712511uL;
        Secret_integers.U64 7435674573564081700uL;
        Secret_integers.U64 2210141511517208575uL;
        Secret_integers.U64 13402431016077863577uL
      ]
    in
    assert_norm (List.Tot.length l == 6);
    Rust_primitives.Hax.array_of_list l)

let g2_simple_swu_iso (u: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp))
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
  let z:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2neg (Hacspec_lib.Traits.Integer.v_TWO, Hacspec_lib.Traits.Integer.v_ONE)
  in
  let a:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 240sz)
  in
  let b:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 1012sz),
    Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 1012sz)
  in
  let tv1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2inv (Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul
                  z
                  z)
              (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul u u)
                  (Hacspec_bls12_381.fp2mul u u)))
          (Hacspec_bls12_381.fp2mul z (Hacspec_bls12_381.fp2mul u u)))
  in
  let x1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2neg b)
          (Hacspec_bls12_381.fp2inv a))
      (Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE) tv1)
  in
  let x1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    if tv1 =. Hacspec_bls12_381.fp2zero
    then
      let x1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
        Hacspec_bls12_381.fp2mul b (Hacspec_bls12_381.fp2inv (Hacspec_bls12_381.fp2mul z a))
      in
      x1
    else x1
  in
  let gx1:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul
                  x1
                  x1)
              x1)
          (Hacspec_bls12_381.fp2mul a x1))
      b
  in
  let x2:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul z (Hacspec_bls12_381.fp2mul u u)) x1
  in
  let gx2:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2add (Hacspec_bls12_381.fp2mul (Hacspec_bls12_381.fp2mul
                  x2
                  x2)
              x2)
          (Hacspec_bls12_381.fp2mul a x2))
      b
  in
  let x, y:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
    if fp2_is_square gx1 then x1, fp2_sqrt gx1 else x2, fp2_sqrt gx2
  in
  let y:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    if fp2_sgn0 u <>. fp2_sgn0 y
    then
      let y:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2neg y in
      y
    else y
  in
  x, y

let g2_isogeny_map (x y: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp))
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let xnum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Seq.new_under_impl_41 4sz
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at xnum_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XNUM_K_0_),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XNUM_K_0_))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at xnum_k
      1sz
      (Hacspec_lib.Traits.Integer.v_ZERO,
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XNUM_K_1_I))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at xnum_k
      2sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XNUM_K_2_R),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XNUM_K_2_I))
  in
  let xnum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at xnum_k
      3sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XNUM_K_3_R),
        Hacspec_lib.Traits.Integer.v_ZERO)
  in
  let xden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Seq.new_under_impl_41 2sz
  in
  let xden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at xden_k
      0sz
      (Hacspec_lib.Traits.Integer.v_ZERO,
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XDEN_K_0_I))
  in
  let xden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at xden_k
      1sz
      (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 12sz),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_XDEN_K_1_I))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Seq.new_under_impl_41 4sz
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at ynum_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YNUM_K_0_),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YNUM_K_0_))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at ynum_k
      1sz
      (Hacspec_lib.Traits.Integer.v_ZERO,
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YNUM_K_1_I))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at ynum_k
      2sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YNUM_K_2_R),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YNUM_K_2_I))
  in
  let ynum_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at ynum_k
      3sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YNUM_K_3_R),
        Hacspec_lib.Traits.Integer.v_ZERO)
  in
  let yden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_lib.Seq.new_under_impl_41 3sz
  in
  let yden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at yden_k
      0sz
      (Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YDEN_K_0_),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YDEN_K_0_))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at yden_k
      1sz
      (Hacspec_lib.Traits.Integer.v_ZERO,
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YDEN_K_1_I))
  in
  let yden_k:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Rust_primitives.Hax.update_at yden_k
      2sz
      (Hacspec_bls12_381.from_literal_under_impl_63 (pub_u128 18sz),
        Hacspec_bls12_381.from_byte_seq_be_under_impl (to_be_bytes_under_impl_69 v_G2_YDEN_K_2_I))
  in
  let xnum:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2zero in
  let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE
  in
  let xnum, xx:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 xnum_k
            }))
      (xnum, xx)
      (fun (xnum, xx) i ->
          let xnum:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2add xnum (Hacspec_bls12_381.fp2mul xx xnum_k.[ i ])
          in
          let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2mul xx x
          in
          xnum, xx)
  in
  let xden:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2zero in
  let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE
  in
  let xden, xx:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 xden_k
            }))
      (xden, xx)
      (fun (xden, xx) i ->
          let xden:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2add xden (Hacspec_bls12_381.fp2mul xx xden_k.[ i ])
          in
          let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2mul xx x
          in
          xden, xx)
  in
  let xden:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2add xden xx in
  let ynum:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2zero in
  let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE
  in
  let xx, ynum:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 ynum_k
            }))
      (xx, ynum)
      (fun (xx, ynum) i ->
          let ynum:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2add ynum (Hacspec_bls12_381.fp2mul xx ynum_k.[ i ])
          in
          let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2mul xx x
          in
          xx, ynum)
  in
  let yden:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2zero in
  let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2fromfp Hacspec_lib.Traits.Integer.v_ONE
  in
  let xx, yden:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 yden_k
            }))
      (xx, yden)
      (fun (xx, yden) i ->
          let yden:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2add yden (Hacspec_bls12_381.fp2mul xx yden_k.[ i ])
          in
          let xx:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
            Hacspec_bls12_381.fp2mul xx x
          in
          xx, yden)
  in
  let yden:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) = Hacspec_bls12_381.fp2add yden xx in
  let xr:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul xnum (Hacspec_bls12_381.fp2inv xden)
  in
  let yr:(Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    Hacspec_bls12_381.fp2mul y (Hacspec_bls12_381.fp2mul ynum (Hacspec_bls12_381.fp2inv yden))
  in
  let inf:bool = false in
  let inf:bool =
    if Prims.op_BarBar (xden =. Hacspec_bls12_381.fp2zero) (yden =. Hacspec_bls12_381.fp2zero)
    then
      let inf:bool = true in
      inf
    else inf
  in
  xr, yr, inf

let g2_map_to_curve_sswu (u: (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp))
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let xp, yp:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp)) =
    g2_simple_swu_iso u
  in
  g2_isogeny_map xp yp

let g2_hash_to_curve_sswu (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let u:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    fp2_hash_to_field msg dst 2sz
  in
  let q0:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    g2_map_to_curve_sswu u.[ 0l ]
  in
  let q1:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    g2_map_to_curve_sswu u.[ 1l ]
  in
  let r:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    Hacspec_bls12_381.g2add q0 q1
  in
  g2_clear_cofactor r

let g2_encode_to_curve_sswu (msg dst: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : ((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
      bool) =
  let u:Hacspec_lib.Seq.t_Seq (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) =
    fp2_hash_to_field msg dst 1sz
  in
  let q:((Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    (Hacspec_bls12_381.t_Fp & Hacspec_bls12_381.t_Fp) &
    bool) =
    g2_map_to_curve_sswu u.[ 0l ]
  in
  g2_clear_cofactor q