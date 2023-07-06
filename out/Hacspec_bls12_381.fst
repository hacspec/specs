module Hacspec_bls12_381
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_fp =
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

unfold
type t_fpcanvas = lseq pub_uint8 384

unfold
type t_serializedfp = lseq uint8 48

unfold
type t_arrayfp = lseq uint_size 6

unfold
type t_scalar = nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000
unfold
type t_scalarcanvas = lseq pub_uint8 256

let t_G1 = (t_Fp & t_Fp & bool)

let t_Fp2 = (t_Fp & t_Fp)

let t_G2 = ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)

let t_Fp6 = ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))

let t_Fp12 =
  (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) & ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))
  )

let fp2fromfp (n: t_Fp) : (t_Fp & t_Fp) = n, Hacspec_lib.Traits.Integer.v_ZERO

let fp2zero: (t_Fp & t_Fp) = fp2fromfp Hacspec_lib.Traits.Integer.v_ZERO

let fp2neg (n: (t_Fp & t_Fp)) : (t_Fp & t_Fp) =
  let n1, n2:(t_Fp & t_Fp) = n in
  Hacspec_lib.Traits.Integer.v_ZERO -. n1, Hacspec_lib.Traits.Integer.v_ZERO -. n2

let fp2add (n m: (t_Fp & t_Fp)) : (t_Fp & t_Fp) =
  let n1, n2:(t_Fp & t_Fp) = n in
  let m1, m2:(t_Fp & t_Fp) = m in
  n1 +. m1, n2 +. m2

let fp2sub (n m: (t_Fp & t_Fp)) : (t_Fp & t_Fp) = fp2add n (fp2neg m)

let fp2mul (n m: (t_Fp & t_Fp)) : (t_Fp & t_Fp) =
  let n1, n2:(t_Fp & t_Fp) = n in
  let m1, m2:(t_Fp & t_Fp) = m in
  let x1 = n1 *. m1 -. n2 *. m2 in
  let x2 = n1 *. m2 +. n2 *. m1 in
  x1, x2

let fp2inv (n: (t_Fp & t_Fp)) : (t_Fp & t_Fp) =
  let n1, n2:(t_Fp & t_Fp) = n in
  let t0 = n1 *. n1 +. n2 *. n2 in
  let t1:t_Fp = inv_under_impl_57 t0 in
  let x1 = n1 *. t1 in
  let x2 = Hacspec_lib.Traits.Integer.v_ZERO -. n2 *. t1 in
  x1, x2

let fp2conjugate (n: (t_Fp & t_Fp)) : (t_Fp & t_Fp) =
  let n1, n2:(t_Fp & t_Fp) = n in
  n1, Hacspec_lib.Traits.Integer.v_ZERO -. n2

let fp6fromfp2 (n: (t_Fp & t_Fp)) : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
  n, fp2zero, fp2zero

let fp6zero: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6fromfp2 fp2zero

let fp6neg (n: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))
    : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
  let n1, n2, n3:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = n in
  fp2sub fp2zero n1, fp2sub fp2zero n2, fp2sub fp2zero n3

let fp6add (n m: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))
    : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
  let n1, n2, n3:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = n in
  let m1, m2, m3:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = m in
  fp2add n1 m1, fp2add n2 m2, fp2add n3 m3

let fp6sub (n m: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))
    : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6add n (fp6neg m)

let fp6mul (n m: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))
    : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
  let n1, n2, n3:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = n in
  let m1, m2, m3:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = m in
  let eps:(t_Fp & t_Fp) = Hacspec_lib.Traits.Integer.v_ONE, Hacspec_lib.Traits.Integer.v_ONE in
  let t1:(t_Fp & t_Fp) = fp2mul n1 m1 in
  let t2:(t_Fp & t_Fp) = fp2mul n2 m2 in
  let t3:(t_Fp & t_Fp) = fp2mul n3 m3 in
  let t4:(t_Fp & t_Fp) = fp2mul (fp2add n2 n3) (fp2add m2 m3) in
  let t5:(t_Fp & t_Fp) = fp2sub (fp2sub t4 t2) t3 in
  let x:(t_Fp & t_Fp) = fp2add (fp2mul t5 eps) t1 in
  let t4:(t_Fp & t_Fp) = fp2mul (fp2add n1 n2) (fp2add m1 m2) in
  let t5:(t_Fp & t_Fp) = fp2sub (fp2sub t4 t1) t2 in
  let y:(t_Fp & t_Fp) = fp2add t5 (fp2mul eps t3) in
  let t4:(t_Fp & t_Fp) = fp2mul (fp2add n1 n3) (fp2add m1 m3) in
  let t5:(t_Fp & t_Fp) = fp2sub (fp2sub t4 t1) t3 in
  let z:(t_Fp & t_Fp) = fp2add t5 t2 in
  x, y, z

let fp6inv (n: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))
    : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
  let n1, n2, n3:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = n in
  let eps:(t_Fp & t_Fp) = Hacspec_lib.Traits.Integer.v_ONE, Hacspec_lib.Traits.Integer.v_ONE in
  let t1:(t_Fp & t_Fp) = fp2mul n1 n1 in
  let t2:(t_Fp & t_Fp) = fp2mul n2 n2 in
  let t3:(t_Fp & t_Fp) = fp2mul n3 n3 in
  let t4:(t_Fp & t_Fp) = fp2mul n1 n2 in
  let t5:(t_Fp & t_Fp) = fp2mul n1 n3 in
  let t6:(t_Fp & t_Fp) = fp2mul n2 n3 in
  let x0:(t_Fp & t_Fp) = fp2sub t1 (fp2mul eps t6) in
  let y0:(t_Fp & t_Fp) = fp2sub (fp2mul eps t3) t4 in
  let z0:(t_Fp & t_Fp) = fp2sub t2 t5 in
  let t0:(t_Fp & t_Fp) = fp2mul n1 x0 in
  let t0:(t_Fp & t_Fp) = fp2add t0 (fp2mul eps (fp2mul n3 y0)) in
  let t0:(t_Fp & t_Fp) = fp2add t0 (fp2mul eps (fp2mul n2 z0)) in
  let t0:(t_Fp & t_Fp) = fp2inv t0 in
  let x:(t_Fp & t_Fp) = fp2mul x0 t0 in
  let y:(t_Fp & t_Fp) = fp2mul y0 t0 in
  let z:(t_Fp & t_Fp) = fp2mul z0 t0 in
  x, y, z

let fp12fromfp6 (n: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) = n, fp6zero

let fp12neg
      (n:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let n1, n2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    n
  in
  fp6sub fp6zero n1, fp6sub fp6zero n2

let fp12add
      (n m:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let n1, n2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    n
  in
  let m1, m2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    m
  in
  fp6add n1 m1, fp6add n2 m2

let fp12sub
      (n m:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) = fp12add n (fp12neg m)

let fp12mul
      (n m:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let n1, n2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    n
  in
  let m1, m2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    m
  in
  let gamma:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
    fp2zero, fp2fromfp Hacspec_lib.Traits.Integer.v_ONE, fp2zero
  in
  let t1:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6mul n1 m1 in
  let t2:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6mul n2 m2 in
  let x:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6add t1 (fp6mul t2 gamma) in
  let y:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6mul (fp6add n1 n2) (fp6add m1 m2) in
  let y:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6sub (fp6sub y t1) t2 in
  x, y

let fp12inv
      (n:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let n1, n2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    n
  in
  let gamma:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) =
    fp2zero, fp2fromfp Hacspec_lib.Traits.Integer.v_ONE, fp2zero
  in
  let t1:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6mul n1 n1 in
  let t2:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6mul n2 n2 in
  let t1:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6sub t1 (fp6mul gamma t2) in
  let t2:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6inv t1 in
  let x:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6mul n1 t2 in
  let y:((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) = fp6neg (fp6mul n2 t2) in
  x, y

let fp12exp
      (n:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
      (k: t_Scalar)
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let c:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12fromfp6 (fp6fromfp2 (fp2fromfp Hacspec_lib.Traits.Integer.v_ONE))
  in
  let c:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 256sz
            }))
      c
      (fun c i ->
          let c:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
            fp12mul c c
          in
          if bit_under_impl_199 k (255sz -. i)
          then
            let c:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
              ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
              fp12mul c n
            in
            c
          else c)
  in
  c

let fp12conjugate
      (n:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let n1, n2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    n
  in
  n1, fp6neg n2

let fp12zero: (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
  ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) = fp12fromfp6 fp6zero

let g1add_a (p q: (t_Fp & t_Fp & bool)) : (t_Fp & t_Fp & bool) =
  let x1, y1, _:(t_Fp & t_Fp & bool) = p in
  let x2, y2, _:(t_Fp & t_Fp & bool) = q in
  let x_diff = x2 -. x1 in
  let y_diff = y2 -. y1 in
  let xovery = y_diff *. inv_under_impl_57 x_diff in
  let x3 = Hacspec_lib.Traits.Numeric.exp xovery 2ul -. x1 -. x2 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_a (p: (t_Fp & t_Fp & bool)) : (t_Fp & t_Fp & bool) =
  let x1, y1, _:(t_Fp & t_Fp & bool) = p in
  let x12:t_Fp = Hacspec_lib.Traits.Numeric.exp x1 2ul in
  let xovery =
    from_literal_under_impl_63 (pub_u128 3sz) *. x12 *.
    inv_under_impl_57 (Hacspec_lib.Traits.Integer.v_TWO *. y1)
  in
  let x3 = Hacspec_lib.Traits.Numeric.exp xovery 2ul -. Hacspec_lib.Traits.Integer.v_TWO *. x1 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double (p: (t_Fp & t_Fp & bool)) : (t_Fp & t_Fp & bool) =
  let _x1, y1, inf1:(t_Fp & t_Fp & bool) = p in
  if Prims.op_AmpAmp (y1 <>. Hacspec_lib.Traits.Integer.v_ZERO) ~.inf1
  then g1double_a p
  else Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1add (p q: (t_Fp & t_Fp & bool)) : (t_Fp & t_Fp & bool) =
  let x1, y1, inf1:(t_Fp & t_Fp & bool) = p in
  let x2, y2, inf2:(t_Fp & t_Fp & bool) = q in
  if inf1
  then q
  else
    if inf2
    then p
    else
      if p =. q
      then g1double p
      else
        if ~.(Prims.op_AmpAmp (x1 =. x2) (y1 =. Hacspec_lib.Traits.Integer.v_ZERO -. y2))
        then g1add_a p q
        else Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1mul (m: t_Scalar) (p: (t_Fp & t_Fp & bool)) : (t_Fp & t_Fp & bool) =
  let t:(t_Fp & t_Fp & bool) =
    Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true
  in
  let t:(t_Fp & t_Fp & bool) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 256sz
            }))
      t
      (fun t i ->
          let t:(t_Fp & t_Fp & bool) = g1double t in
          if bit_under_impl_199 m (255sz -. i)
          then
            let t:(t_Fp & t_Fp & bool) = g1add t p in
            t
          else t)
  in
  t

let g1neg (p: (t_Fp & t_Fp & bool)) : (t_Fp & t_Fp & bool) =
  let x, y, inf:(t_Fp & t_Fp & bool) = p in
  x, Hacspec_lib.Traits.Integer.v_ZERO -. y, inf

let g2add_a (p q: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
  let x1, y1, _:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = p in
  let x2, y2, _:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = q in
  let x_diff:(t_Fp & t_Fp) = fp2sub x2 x1 in
  let y_diff:(t_Fp & t_Fp) = fp2sub y2 y1 in
  let xovery:(t_Fp & t_Fp) = fp2mul y_diff (fp2inv x_diff) in
  let t1:(t_Fp & t_Fp) = fp2mul xovery xovery in
  let t2:(t_Fp & t_Fp) = fp2sub t1 x1 in
  let x3:(t_Fp & t_Fp) = fp2sub t2 x2 in
  let t1:(t_Fp & t_Fp) = fp2sub x1 x3 in
  let t2:(t_Fp & t_Fp) = fp2mul xovery t1 in
  let y3:(t_Fp & t_Fp) = fp2sub t2 y1 in
  x3, y3, false

let g2double_a (p: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
  let x1, y1, _:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = p in
  let x12:(t_Fp & t_Fp) = fp2mul x1 x1 in
  let t1:(t_Fp & t_Fp) = fp2mul (fp2fromfp (from_literal_under_impl_63 (pub_u128 3sz))) x12 in
  let t2:(t_Fp & t_Fp) = fp2inv (fp2mul (fp2fromfp Hacspec_lib.Traits.Integer.v_TWO) y1) in
  let xovery:(t_Fp & t_Fp) = fp2mul t1 t2 in
  let t1:(t_Fp & t_Fp) = fp2mul xovery xovery in
  let t2:(t_Fp & t_Fp) = fp2mul (fp2fromfp Hacspec_lib.Traits.Integer.v_TWO) x1 in
  let x3:(t_Fp & t_Fp) = fp2sub t1 t2 in
  let t1:(t_Fp & t_Fp) = fp2sub x1 x3 in
  let t2:(t_Fp & t_Fp) = fp2mul xovery t1 in
  let y3:(t_Fp & t_Fp) = fp2sub t2 y1 in
  x3, y3, false

let g2double (p: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
  let _x1, y1, inf1:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = p in
  if Prims.op_AmpAmp (y1 <>. fp2zero) ~.inf1 then g2double_a p else fp2zero, fp2zero, true

let g2add (p q: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
  let x1, y1, inf1:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = p in
  let x2, y2, inf2:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = q in
  if inf1
  then q
  else
    if inf2
    then p
    else
      if p =. q
      then g2double p
      else
        if ~.(Prims.op_AmpAmp (x1 =. x2) (y1 =. fp2neg y2))
        then g2add_a p q
        else fp2zero, fp2zero, true

let g2mul (m: t_Scalar) (p: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool))
    : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
  let t:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = fp2zero, fp2zero, true in
  let t:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 256sz
            }))
      t
      (fun t i ->
          let t:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = g2double t in
          if bit_under_impl_199 m (255sz -. i)
          then
            let t:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = g2add t p in
            t
          else t)
  in
  t

let g2neg (p: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) : ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) =
  let x, y, inf:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = p in
  x, fp2neg y, inf

let twist (p: (t_Fp & t_Fp & bool))
    : ((((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
        ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) &
      (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
        ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))) =
  let p0, p1, _:(t_Fp & t_Fp & bool) = p in
  let x:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    FStar.Pervasives.Native.Mktuple3 fp2zero (fp2fromfp p0) fp2zero, fp6zero
  in
  let y:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp6zero, FStar.Pervasives.Native.Mktuple3 fp2zero (fp2fromfp p1) fp2zero
  in
  x, y

let line_double_p (r: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) (p: (t_Fp & t_Fp & bool))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let r0, r1, _:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = r in
  let a:(t_Fp & t_Fp) =
    fp2mul (fp2fromfp (from_literal_under_impl_63 (pub_u128 3sz))) (fp2mul r0 r0)
  in
  let a:(t_Fp & t_Fp) =
    fp2mul a (fp2inv (fp2mul (fp2fromfp Hacspec_lib.Traits.Integer.v_TWO) r1))
  in
  let b:(t_Fp & t_Fp) = fp2sub r1 (fp2mul a r0) in
  let a:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12fromfp6 (fp6fromfp2 a)
  in
  let b:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12fromfp6 (fp6fromfp2 b)
  in
  let x, y:((((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) &
    (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))) =
    twist p
  in
  fp12neg (fp12sub (fp12sub y (fp12mul a x)) b)

let line_add_p (r q: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) (p: (t_Fp & t_Fp & bool))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let r0, r1, _:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = r in
  let q0, q1, _:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = q in
  let a:(t_Fp & t_Fp) = fp2mul (fp2sub q1 r1) (fp2inv (fp2sub q0 r0)) in
  let b:(t_Fp & t_Fp) = fp2sub r1 (fp2mul a r0) in
  let a:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12fromfp6 (fp6fromfp2 a)
  in
  let b:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12fromfp6 (fp6fromfp2 b)
  in
  let x, y:((((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) &
    (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)))) =
    twist p
  in
  fp12neg (fp12sub (fp12sub y (fp12mul a x)) b)

let frobenius
      (f:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let (g0, g1, g2), (h0, h1, h2):(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    f
  in
  let t1:(t_Fp & t_Fp) = fp2conjugate g0 in
  let t2:(t_Fp & t_Fp) = fp2conjugate h0 in
  let t3:(t_Fp & t_Fp) = fp2conjugate g1 in
  let t4:(t_Fp & t_Fp) = fp2conjugate h1 in
  let t5:(t_Fp & t_Fp) = fp2conjugate g2 in
  let t6:(t_Fp & t_Fp) = fp2conjugate h2 in
  let c1:t_ArrayFp =
    ArrayFp
    (let l =
        [
          Secret_integers.U64 10162220747404304312uL;
          Secret_integers.U64 17761815663483519293uL;
          Secret_integers.U64 8873291758750579140uL;
          Secret_integers.U64 1141103941765652303uL;
          Secret_integers.U64 13993175198059990303uL;
          Secret_integers.U64 1802798568193066599uL
        ]
      in
      assert_norm (List.Tot.length l == 6);
      Rust_primitives.Hax.array_of_list l)
  in
  let c1:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = to_le_bytes_under_impl_104 c1 in
  let c1:t_Fp = from_byte_seq_le_under_impl c1 in
  let c2:t_ArrayFp =
    ArrayFp
    (let l =
        [
          Secret_integers.U64 3240210268673559283uL;
          Secret_integers.U64 2895069921743240898uL;
          Secret_integers.U64 17009126888523054175uL;
          Secret_integers.U64 6098234018649060207uL;
          Secret_integers.U64 9865672654120263608uL;
          Secret_integers.U64 71000049454473266uL
        ]
      in
      assert_norm (List.Tot.length l == 6);
      Rust_primitives.Hax.array_of_list l)
  in
  let c2:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = to_le_bytes_under_impl_104 c2 in
  let c2:t_Fp = from_byte_seq_le_under_impl c2 in
  let gamma11:(t_Fp & t_Fp) = c1, c2 in
  let gamma12:(t_Fp & t_Fp) = fp2mul gamma11 gamma11 in
  let gamma13:(t_Fp & t_Fp) = fp2mul gamma12 gamma11 in
  let gamma14:(t_Fp & t_Fp) = fp2mul gamma13 gamma11 in
  let gamma15:(t_Fp & t_Fp) = fp2mul gamma14 gamma11 in
  let t2:(t_Fp & t_Fp) = fp2mul t2 gamma11 in
  let t3:(t_Fp & t_Fp) = fp2mul t3 gamma12 in
  let t4:(t_Fp & t_Fp) = fp2mul t4 gamma13 in
  let t5:(t_Fp & t_Fp) = fp2mul t5 gamma14 in
  let t6:(t_Fp & t_Fp) = fp2mul t6 gamma15 in
  FStar.Pervasives.Native.Mktuple3 t1 t3 t5, FStar.Pervasives.Native.Mktuple3 t2 t4 t6

let final_exponentiation
      (f:
          (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let fp6:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate f
  in
  let finv:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12inv f
  in
  let fp6_1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul fp6 finv
  in
  let fp8:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    frobenius (frobenius fp6_1)
  in
  let f:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul fp8 fp6_1
  in
  let u:t_Scalar = from_literal_under_impl_199 (pub_u128 15132376222941642752sz) in
  let u_half:t_Scalar = from_literal_under_impl_199 (pub_u128 7566188111470821376sz) in
  let t0:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul f f
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12exp t0 u
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t1
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12exp t1 u_half
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t2
  in
  let t3:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate f
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t3 t1
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t1
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t1 t2
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12exp t1 u
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t2
  in
  let t3:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12exp t2 u
  in
  let t3:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t3
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t1
  in
  let t3:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t1 t3
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t1
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    frobenius (frobenius (frobenius t1))
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    frobenius (frobenius t2)
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t1 t2
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12exp t3 u
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12conjugate t2
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t2 t0
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t2 f
  in
  let t1:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12mul t1 t2
  in
  let t2:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    frobenius t3
  in
  fp12mul t1 t2

let pairing (p: (t_Fp & t_Fp & bool)) (q: ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool))
    : (((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
  let t:t_Scalar = from_literal_under_impl_199 (pub_u128 15132376222941642752sz) in
  let r:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = q in
  let f:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
    fp12fromfp6 (fp6fromfp2 (fp2fromfp Hacspec_lib.Traits.Integer.v_ONE))
  in
  let f, r:((((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
      ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) &
    ((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 1sz;
              Core.Ops.Range.Range.f_end = 64sz
            }))
      (f, r)
      (fun (f, r) i ->
          let lrr:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
            line_double_p r p
          in
          let r:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = g2double r in
          let f:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
            ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
            fp12mul (fp12mul f f) lrr
          in
          if bit_under_impl_199 t (64sz -. i -. 1sz)
          then
            let lrq:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
              ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
              line_add_p r q p
            in
            let r:((t_Fp & t_Fp) & (t_Fp & t_Fp) & bool) = g2add r q in
            let f:(((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp)) &
              ((t_Fp & t_Fp) & (t_Fp & t_Fp) & (t_Fp & t_Fp))) =
              fp12mul f lrq
            in
            f, r
          else f, r)
  in
  final_exponentiation (fp12conjugate f)