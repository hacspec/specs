module Hacspec_pasta
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_fppallas = nat_mod 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
unfold
type t_pallascanvas = lseq pub_uint8 255

unfold
type t_fpvesta = nat_mod 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
unfold
type t_vestacanvas = lseq pub_uint8 255

let t_G1_pallas = (t_FpPallas & t_FpPallas & bool)

let t_G1_vesta = (t_FpVesta & t_FpVesta & bool)

let g1_default_pallas: (t_FpPallas & t_FpPallas & bool) =
  Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1_default_vesta: (t_FpVesta & t_FpVesta & bool) =
  Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1add_a_pallas (p q: (t_FpPallas & t_FpPallas & bool)) : (t_FpPallas & t_FpPallas & bool) =
  let x1, y1, _:(t_FpPallas & t_FpPallas & bool) = p in
  let x2, y2, _:(t_FpPallas & t_FpPallas & bool) = q in
  let x_diff = x2 -. x1 in
  let y_diff = y2 -. y1 in
  let xovery = y_diff *. inv_under_impl_57 x_diff in
  let x3 = Hacspec_lib.Traits.Numeric.exp xovery 2ul -. x1 -. x2 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1add_a_vesta (p q: (t_FpVesta & t_FpVesta & bool)) : (t_FpVesta & t_FpVesta & bool) =
  let x1, y1, _:(t_FpVesta & t_FpVesta & bool) = p in
  let x2, y2, _:(t_FpVesta & t_FpVesta & bool) = q in
  let x_diff = x2 -. x1 in
  let y_diff = y2 -. y1 in
  let xovery = y_diff *. inv_under_impl_124 x_diff in
  let x3 = Hacspec_lib.Traits.Numeric.exp xovery 2ul -. x1 -. x2 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_a_pallas (p: (t_FpPallas & t_FpPallas & bool)) : (t_FpPallas & t_FpPallas & bool) =
  let x1, y1, _:(t_FpPallas & t_FpPallas & bool) = p in
  let x12:t_FpPallas = Hacspec_lib.Traits.Numeric.exp x1 2ul in
  let xovery =
    from_literal_under_impl_63 (pub_u128 3sz) *. x12 *.
    inv_under_impl_57 (Hacspec_lib.Traits.Integer.v_TWO *. y1)
  in
  let x3 = Hacspec_lib.Traits.Numeric.exp xovery 2ul -. Hacspec_lib.Traits.Integer.v_TWO *. x1 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_a_vesta (p: (t_FpVesta & t_FpVesta & bool)) : (t_FpVesta & t_FpVesta & bool) =
  let x1, y1, _:(t_FpVesta & t_FpVesta & bool) = p in
  let x12:t_FpVesta = Hacspec_lib.Traits.Numeric.exp x1 2ul in
  let xovery =
    from_literal_under_impl_130 (pub_u128 3sz) *. x12 *.
    inv_under_impl_124 (Hacspec_lib.Traits.Integer.v_TWO *. y1)
  in
  let x3 = Hacspec_lib.Traits.Numeric.exp xovery 2ul -. Hacspec_lib.Traits.Integer.v_TWO *. x1 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_pallas (p: (t_FpPallas & t_FpPallas & bool)) : (t_FpPallas & t_FpPallas & bool) =
  let _x1, y1, inf1:(t_FpPallas & t_FpPallas & bool) = p in
  if Prims.op_AmpAmp (y1 <>. Hacspec_lib.Traits.Integer.v_ZERO) ~.inf1
  then g1double_a_pallas p
  else Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1double_vesta (p: (t_FpVesta & t_FpVesta & bool)) : (t_FpVesta & t_FpVesta & bool) =
  let _x1, y1, inf1:(t_FpVesta & t_FpVesta & bool) = p in
  if Prims.op_AmpAmp (y1 <>. Hacspec_lib.Traits.Integer.v_ZERO) ~.inf1
  then g1double_a_vesta p
  else Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1add_pallas (p q: (t_FpPallas & t_FpPallas & bool)) : (t_FpPallas & t_FpPallas & bool) =
  let x1, y1, inf1:(t_FpPallas & t_FpPallas & bool) = p in
  let x2, y2, inf2:(t_FpPallas & t_FpPallas & bool) = q in
  if inf1
  then q
  else
    if inf2
    then p
    else
      if p =. q
      then g1double_pallas p
      else
        if ~.(Prims.op_AmpAmp (x1 =. x2) (y1 =. Hacspec_lib.Traits.Integer.v_ZERO -. y2))
        then g1add_a_pallas p q
        else Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1add_vesta (p q: (t_FpVesta & t_FpVesta & bool)) : (t_FpVesta & t_FpVesta & bool) =
  let x1, y1, inf1:(t_FpVesta & t_FpVesta & bool) = p in
  let x2, y2, inf2:(t_FpVesta & t_FpVesta & bool) = q in
  if inf1
  then q
  else
    if inf2
    then p
    else
      if p =. q
      then g1double_vesta p
      else
        if ~.(Prims.op_AmpAmp (x1 =. x2) (y1 =. Hacspec_lib.Traits.Integer.v_ZERO -. y2))
        then g1add_a_vesta p q
        else Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true

let g1mul_pallas (m: t_FpVesta) (p: (t_FpPallas & t_FpPallas & bool))
    : (t_FpPallas & t_FpPallas & bool) =
  let t:(t_FpPallas & t_FpPallas & bool) =
    Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true
  in
  let t:(t_FpPallas & t_FpPallas & bool) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 255sz
            }))
      t
      (fun t i ->
          let t:(t_FpPallas & t_FpPallas & bool) = g1double_pallas t in
          if bit_under_impl_130 m (254sz -. i)
          then
            let t:(t_FpPallas & t_FpPallas & bool) = g1add_pallas t p in
            t
          else t)
  in
  t

let g1mul_vesta (m: t_FpPallas) (p: (t_FpVesta & t_FpVesta & bool)) : (t_FpVesta & t_FpVesta & bool) =
  let t:(t_FpVesta & t_FpVesta & bool) =
    Hacspec_lib.Traits.Integer.v_ZERO, Hacspec_lib.Traits.Integer.v_ZERO, true
  in
  let t:(t_FpVesta & t_FpVesta & bool) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 255sz
            }))
      t
      (fun t i ->
          let t:(t_FpVesta & t_FpVesta & bool) = g1double_vesta t in
          if bit_under_impl_63 m (254sz -. i)
          then
            let t:(t_FpVesta & t_FpVesta & bool) = g1add_vesta t p in
            t
          else t)
  in
  t

let g1neg_pallas (p: (t_FpPallas & t_FpPallas & bool)) : (t_FpPallas & t_FpPallas & bool) =
  let x, y, inf:(t_FpPallas & t_FpPallas & bool) = p in
  x, Hacspec_lib.Traits.Integer.v_ZERO -. y, inf

let g1neg_vesta (p: (t_FpVesta & t_FpVesta & bool)) : (t_FpVesta & t_FpVesta & bool) =
  let x, y, inf:(t_FpVesta & t_FpVesta & bool) = p in
  x, Hacspec_lib.Traits.Integer.v_ZERO -. y, inf

let g1_on_curve_pallas (p: (t_FpPallas & t_FpPallas & bool)) : bool =
  let x, y, inf:(t_FpPallas & t_FpPallas & bool) = p in
  let y_squared = y *. y in
  let x_cubed = x *. x *. x in
  let fp5 =
    Hacspec_lib.Traits.Integer.v_TWO +. Hacspec_lib.Traits.Integer.v_TWO +.
    Hacspec_lib.Traits.Integer.v_ONE
  in
  Prims.op_BarBar (y_squared =. x_cubed +. fp5) inf

let g1_on_curve_vesta (p: (t_FpVesta & t_FpVesta & bool)) : bool =
  let x, y, inf:(t_FpVesta & t_FpVesta & bool) = p in
  let y_squared = y *. y in
  let x_cubed = x *. x *. x in
  let fp5 =
    Hacspec_lib.Traits.Integer.v_TWO +. Hacspec_lib.Traits.Integer.v_TWO +.
    Hacspec_lib.Traits.Integer.v_ONE
  in
  Prims.op_BarBar (y_squared =. x_cubed +. fp5) inf

let g1_is_identity_pallas (p: (t_FpPallas & t_FpPallas & bool)) : bool =
  let _, _, inf:(t_FpPallas & t_FpPallas & bool) = p in
  inf

let g1_is_identity_vesta (p: (t_FpVesta & t_FpVesta & bool)) : bool =
  let _, _, inf:(t_FpVesta & t_FpVesta & bool) = p in
  inf