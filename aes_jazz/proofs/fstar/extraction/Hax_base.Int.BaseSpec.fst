module Hax_base.Int.BaseSpec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
// open Core
open FStar.Mul

let impl__clone (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = self

let impl__dealloc (self: Hax_base.Int.t_HaxInt) : Prims.unit =
  ()

let impl_1__xH: Hax_base.Int.t_HaxInt = 1

let impl_1__xI (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = self * 2 + 1

let impl_1__xO (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = self * 2

let impl_2__ZERO: Hax_base.Int.t_HaxInt = 0

let impl__normalize (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = self

let impl_1__div2 (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = self / 2

let impl_1__is_xH (self: Hax_base.Int.t_HaxInt) : bool = self = 1

let impl_1__is_xI (self: Hax_base.Int.t_HaxInt) : bool = self > 1 && self % 2 = 1

let impl_1__is_xO (self: Hax_base.Int.t_HaxInt) : bool = self > 1 && self % 2 = 0

let impl_2__is_zero (self: Hax_base.Int.t_HaxInt) : bool = self = 0

let impl_2__pred (self: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires not (impl_2__is_zero self <: bool))
      (fun _ -> Prims.l_True) =
      self - 1

let impl_2__succ (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = self + 1

let v_WORDSIZE_128_: Hax_base.Int.t_HaxInt = pow2 128

let v_WORDSIZE_128_SUB_1_: Hax_base.Int.t_HaxInt = v_WORDSIZE_128_ - 1

let v_WORDSIZE_16_: Hax_base.Int.t_HaxInt = pow2 16

let v_WORDSIZE_16_SUB_1_: Hax_base.Int.t_HaxInt = v_WORDSIZE_16_ - 1

let v_WORDSIZE_32_: Hax_base.Int.t_HaxInt = pow2 32

let v_WORDSIZE_32_SUB_1_: Hax_base.Int.t_HaxInt = v_WORDSIZE_32_ - 1

let v_WORDSIZE_64_: Hax_base.Int.t_HaxInt = pow2 64

let v_WORDSIZE_64_SUB_1_: Hax_base.Int.t_HaxInt = v_WORDSIZE_64_ - 1

let v_WORDSIZE_8_: Hax_base.Int.t_HaxInt = pow2 8

let v_WORDSIZE_8_SUB_1_: Hax_base.Int.t_HaxInt = v_WORDSIZE_8_ - 1

let impl_1__match_pos (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_POS =
  if impl_2__is_zero (impl__clone self <: Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = impl__dealloc self in
    Hax_base.Int.POS_ZERO <: Hax_base.Int.t_POS
  else Hax_base.Int.POS_POS self <: Hax_base.Int.t_POS

let impl_1__match_positive (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_POSITIVE =
  if impl_1__is_xH (impl__clone self <: Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = impl__dealloc self in
    Hax_base.Int.POSITIVE_XH <: Hax_base.Int.t_POSITIVE
  else
    if impl_1__is_xO (impl__clone self <: Hax_base.Int.t_HaxInt)
    then Hax_base.Int.POSITIVE_XO (impl_1__div2 self) <: Hax_base.Int.t_POSITIVE
    else Hax_base.Int.POSITIVE_XI (impl_1__div2 self) <: Hax_base.Int.t_POSITIVE

let impl_2__match_unary (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_UNARY =
  if impl_2__is_zero (impl__clone self <: Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = impl__dealloc self in
    Hax_base.Int.UNARY_ZERO <: Hax_base.Int.t_UNARY
  else Hax_base.Int.UNARY_SUCC (impl_2__pred self) <: Hax_base.Int.t_UNARY
