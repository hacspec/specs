module Hax_base.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
// open Core
open FStar.Mul

let discriminant_CMP_EQ = 0

let discriminant_CMP_GREATER = 1

type t_CMP =
  | CMP_LESS : t_CMP
  | CMP_EQ : t_CMP
  | CMP_GREATER : t_CMP

let impl__CMP__clone (self: t_CMP) : t_CMP =
  match self with
  | CMP_LESS  -> CMP_LESS <: t_CMP
  | CMP_EQ  -> CMP_EQ <: t_CMP
  | CMP_GREATER  -> CMP_GREATER <: t_CMP

let impl__CMP__eq (self rhs: t_CMP) : bool =
  match self, rhs <: (t_CMP & t_CMP) with
  | CMP_LESS , CMP_LESS  | CMP_EQ , CMP_EQ  | CMP_GREATER , CMP_GREATER  -> true
  | _ -> false

let discriminant_CMP_LESS = (-1)

let t_CMP_cast_to_repr (x: t_CMP) =
  match x with
  | CMP_LESS  -> discriminant_CMP_LESS
  | CMP_EQ  -> discriminant_CMP_EQ
  | CMP_GREATER  -> discriminant_CMP_GREATER

type t_HaxInt = Prims.nat

type t_POS =
  | POS_ZERO : t_POS
  | POS_POS : t_HaxInt -> t_POS

type t_POSITIVE =
  | POSITIVE_XH : t_POSITIVE
  | POSITIVE_XO : t_HaxInt -> t_POSITIVE
  | POSITIVE_XI : t_HaxInt -> t_POSITIVE

type t_UNARY =
  | UNARY_ZERO : t_UNARY
  | UNARY_SUCC : t_HaxInt -> t_UNARY
