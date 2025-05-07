module Hax_core.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
// open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_base.Int in
  ()

class t_Constants (v_Self: Type0) = {
  f_ZERO:v_Self;
  f_ONE:v_Self;
  f_MIN:v_Self;
  f_MAX:v_Self
}

type t_U128 = { f_v:Hax_base.Int.t_HaxInt }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_108: t_Constants t_U128 =
  {
    f_ZERO = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U128;
    f_ONE = { f_v = Hax_base.Int.BaseSpec.impl_1__xH } <: t_U128;
    f_MIN = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U128; // f_ZERO;
    f_MAX = { f_v = Hax_base.Int.BaseSpec.v_WORDSIZE_128_SUB_1_ } <: t_U128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_110: Hax_core.Coerce.t_Concretization Hax_base.Int.t_HaxInt t_U128 =
  {
    f_concretize_pre = (fun (self: Hax_base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Hax_base.Int.t_HaxInt) (out: t_U128) -> true);
    f_concretize
    =
    fun (self: Hax_base.Int.t_HaxInt) ->
      { f_v = Hax_base.Int.BaseImpl.impl__rem self Hax_base.Int.BaseSpec.v_WORDSIZE_128_ } <: t_U128
  }

let impl_111__checked_concretize (x: Hax_base.Int.t_HaxInt) : option // Core.Option.t_Option
  t_U128 =
  if
    Hax_base.Int.BaseImpl.impl__lt (// Core.Clone.f_clone #Hax_base.Int.t_HaxInt
          // #FStar.Tactics.Typeclasses.solve
          x
        <:
        Hax_base.Int.t_HaxInt)
      Hax_base.Int.BaseSpec.v_WORDSIZE_128_
  then // Core.Option.Option_Some
  Some
  ({ f_v = x } <: t_U128) <: // Core.Option.t_Option
  option
  t_U128
  else // Core.Option.Option_None
  None
  <: // Core.Option.t_Option
  option t_U128

let impl_111__wrapping_concretize (x: Hax_base.Int.t_HaxInt) : t_U128 =
  { f_v = Hax_base.Int.BaseImpl.impl__rem x Hax_base.Int.BaseSpec.v_WORDSIZE_128_ } <: t_U128

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_115: // Core.Clone.t_Clone
//   t_U128 =
//   {
//     f_clone_pre = (fun (self: t_U128) -> true);
//     f_clone_post = (fun (self: t_U128) (out: t_U128) -> true);
//     f_clone
//     =
//     fun (self: t_U128) ->
//       { f_v = // 
//   self.f_v }
//       <:
//       t_U128
//   }

type t_U16 = { f_v:Hax_base.Int.t_HaxInt }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: t_Constants t_U16 =
  {
    f_ZERO = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U16;
    f_ONE = { f_v = Hax_base.Int.BaseSpec.impl_1__xH } <: t_U16;
    f_MIN = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U16; // f_ZERO;
    f_MAX = { f_v = Hax_base.Int.BaseSpec.v_WORDSIZE_16_SUB_1_ } <: t_U16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Hax_core.Coerce.t_Concretization Hax_base.Int.t_HaxInt t_U16 =
  {
    f_concretize_pre = (fun (self: Hax_base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Hax_base.Int.t_HaxInt) (out: t_U16) -> true);
    f_concretize
    =
    fun (self: Hax_base.Int.t_HaxInt) ->
      { f_v = Hax_base.Int.BaseImpl.impl__rem self Hax_base.Int.BaseSpec.v_WORDSIZE_16_ } <: t_U16
  }

let impl_30__checked_concretize (x: Hax_base.Int.t_HaxInt) : // Core.Option.t_Option
 option t_U16 =
  if
    Hax_base.Int.BaseImpl.impl__lt (
    // Core.Clone.f_clone #Hax_base.Int.t_HaxInt
          // #FStar.Tactics.Typeclasses.solve
          x
        <:
        Hax_base.Int.t_HaxInt)
      Hax_base.Int.BaseSpec.v_WORDSIZE_16_
  then // Core.Option.Option_Some
  Some ({ f_v = x } <: t_U16) <: // Core.Option.t_Option
   option t_U16
  else // Core.Option.Option_None
  None <: // Core.Option.t_Option
   option t_U16

let impl_30__wrapping_concretize (x: Hax_base.Int.t_HaxInt) : t_U16 =
  { f_v = Hax_base.Int.BaseImpl.impl__rem x Hax_base.Int.BaseSpec.v_WORDSIZE_16_ } <: t_U16

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_34: Core.Clone.t_Clone t_U16 =
//   {
//     f_clone_pre = (fun (self: t_U16) -> true);
//     f_clone_post = (fun (self: t_U16) (out: t_U16) -> true);
//     f_clone
//     =
//     fun (self: t_U16) ->
//       { f_v =  self.f_v }
//       <:
//       t_U16
//   }

type t_U32 = { f_v:Hax_base.Int.t_HaxInt }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: t_Constants t_U32 =
  {
    f_ZERO = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U32;
    f_ONE = { f_v = Hax_base.Int.BaseSpec.impl_1__xH } <: t_U32;
    f_MIN = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } ; // f_ZERO;
    f_MAX = { f_v = Hax_base.Int.BaseSpec.v_WORDSIZE_32_SUB_1_ } <: t_U32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Hax_core.Coerce.t_Concretization Hax_base.Int.t_HaxInt t_U32 =
  {
    f_concretize_pre = (fun (self: Hax_base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Hax_base.Int.t_HaxInt) (out: t_U32) -> true);
    f_concretize
    =
    fun (self: Hax_base.Int.t_HaxInt) ->
      { f_v = Hax_base.Int.BaseImpl.impl__rem self Hax_base.Int.BaseSpec.v_WORDSIZE_32_ } <: t_U32
  }

let impl_57__checked_concretize (x: Hax_base.Int.t_HaxInt) : // Core.Option.t_Option
 option t_U32 =
  if
    Hax_base.Int.BaseImpl.impl__lt (
          x
        <:
        Hax_base.Int.t_HaxInt)
      Hax_base.Int.BaseSpec.v_WORDSIZE_32_
  then // Core.Option.Option_Some
  Some ({ f_v = x } <: t_U32) <: // Core.Option.t_Option
   option t_U32
  else // Core.Option.Option_None
  None <: // Core.Option.t_Option
   option t_U32

let impl_57__wrapping_concretize (x: Hax_base.Int.t_HaxInt) : t_U32 =
  { f_v = Hax_base.Int.BaseImpl.impl__rem x Hax_base.Int.BaseSpec.v_WORDSIZE_32_ } <: t_U32

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_61: t_U32 =
//   {
//     f_clone_pre = (fun (self: t_U32) -> true);
//     f_clone_post = (fun (self: t_U32) (out: t_U32) -> true);
//     f_clone
//     =
//     fun (self: t_U32) ->
//       { f_v =  self.f_v }
//       <:
//       t_U32
//   }

type t_U64 = { f_v:Hax_base.Int.t_HaxInt }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_81: t_Constants t_U64 =
  {
    f_ZERO = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U64;
    f_ONE = { f_v = Hax_base.Int.BaseSpec.impl_1__xH } <: t_U64;
    f_MIN = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO }; // f_ZERO;
    f_MAX = { f_v = Hax_base.Int.BaseSpec.v_WORDSIZE_64_SUB_1_ } <: t_U64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_83: Hax_core.Coerce.t_Concretization Hax_base.Int.t_HaxInt t_U64 =
  {
    f_concretize_pre = (fun (self: Hax_base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Hax_base.Int.t_HaxInt) (out: t_U64) -> true);
    f_concretize
    =
    fun (self: Hax_base.Int.t_HaxInt) ->
      { f_v = Hax_base.Int.BaseImpl.impl__rem self Hax_base.Int.BaseSpec.v_WORDSIZE_64_ } <: t_U64
  }

let impl_84__checked_concretize (x: Hax_base.Int.t_HaxInt) : // Core.Option.t_Option
 option t_U64 =
  if
    Hax_base.Int.BaseImpl.impl__lt (
          x
        <:
        Hax_base.Int.t_HaxInt)
      Hax_base.Int.BaseSpec.v_WORDSIZE_64_
  then // Core.Option.Option_Some
  Some ({ f_v
  = x } <: t_U64) <: // Core.Option.t_Option
   option t_U64
  else // Core.Option.Option_None
  None <: // Core.Option.t_Option
   option t_U64

let impl_84__wrapping_concretize (x: Hax_base.Int.t_HaxInt) : t_U64 =
  { f_v = Hax_base.Int.BaseImpl.impl__rem x Hax_base.Int.BaseSpec.v_WORDSIZE_64_ } <: t_U64

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_88: t_U64 =
//   {
//     f_clone_pre = (fun (self: t_U64) -> true);
//     f_clone_post = (fun (self: t_U64) (out: t_U64) -> true);
//     f_clone
//     =
//     fun (self: t_U64) ->
//       { f_v =  self.f_v }
//       <:
//       t_U64
//   }

type t_U8 = { f_v:Hax_base.Int.t_HaxInt }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Constants t_U8 =
  {
    f_ZERO = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO } <: t_U8;
    f_ONE = { f_v = Hax_base.Int.BaseSpec.impl_1__xH } <: t_U8;
    f_MIN = { f_v = Hax_base.Int.BaseSpec.impl_2__ZERO };
    f_MAX = { f_v = Hax_base.Int.BaseSpec.v_WORDSIZE_8_SUB_1_ } <: t_U8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Hax_core.Coerce.t_Concretization Hax_base.Int.t_HaxInt t_U8 =
  {
    f_concretize_pre = (fun (self: Hax_base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Hax_base.Int.t_HaxInt) (out: t_U8) -> true);
    f_concretize
    =
    fun (self: Hax_base.Int.t_HaxInt) ->
      { f_v = Hax_base.Int.BaseImpl.impl__rem self Hax_base.Int.BaseSpec.v_WORDSIZE_8_ } <: t_U8
  }

let impl_3__checked_concretize (x: Hax_base.Int.t_HaxInt) : // Core.Option.t_Option
 option t_U8 =
  if
    Hax_base.Int.BaseImpl.impl__lt (
          x
        <:
        Hax_base.Int.t_HaxInt)
      Hax_base.Int.BaseSpec.v_WORDSIZE_8_
  then Some // Core.Option.Option_Some
  ({ f_v
  = x } <: t_U8) <: // Core.Option.t_Option
   option t_U8
  else // Core.Option.Option_None
  None <: // Core.Option.t_Option
   option t_U8

let impl_3__wrapping_concretize (x: Hax_base.Int.t_HaxInt) : t_U8 =
  { f_v = Hax_base.Int.BaseImpl.impl__rem x Hax_base.Int.BaseSpec.v_WORDSIZE_8_ } <: t_U8

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_7: Core.Clone.t_Clone t_U8 =
//   {
//     f_clone_pre = (fun (self: t_U8) -> true);
//     f_clone_post = (fun (self: t_U8) (out: t_U8) -> true);
//     f_clone
//     =
//     fun (self: t_U8) ->
//       { f_v =  self.f_v }
//       <:
//       t_U8
//   }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Hax_core.Coerce.t_Abstraction t_U8 =
  {
    f_AbstractType = Hax_base.Int.t_HaxInt;
    f_lift_pre = (fun (self: t_U8) -> true);
    f_lift_post = (fun (self: t_U8) (out: Hax_base.Int.t_HaxInt) -> true);
    f_lift = fun (self: t_U8) -> self.f_v
  }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_8: Core.Cmp.t_PartialEq t_U8 t_U8 =
//   {
//     f_eq_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_eq_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
//     f_eq
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_base.Int.BaseImpl.impl__eq (Hax_core.Coerce.f_lift #t_U8
//             #FStar.Tactics.Typeclasses.solve
//             (self <: t_U8)
//           <:
//           Hax_base.Int.t_HaxInt)
//         (Hax_core.Coerce.f_lift #t_U8
//             #FStar.Tactics.Typeclasses.solve
//             (rhs <: t_U8)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_9: Core.Cmp.t_PartialOrd t_U8 t_U8 =
//   {
//     _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
//     f_partial_cmp_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_partial_cmp_post
//     =
//     (fun (self: t_U8) (rhs: t_U8) (out: // Core.Option.t_Option
//      option Core.Cmp.t_Ordering) -> true);
//     f_partial_cmp
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Core.Option.// Option_Some
//       (match
//           Hax
//           Some _base.Int.BaseImpl.impl__cmp (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
//               <:
//               Hax_base.Int.t_HaxInt)
//         with
//         | Hax_base.Int.CMP_LESS  -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_EQ  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_GREATER  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
//       <:
//       // Core.Option.t_Option
//        option Core.Cmp.t_Ordering
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_28: Hax_core.Coerce.t_Abstraction t_U16 =
//   {
//     f_AbstractType = Hax_base.Int.t_HaxInt;
//     f_lift_pre = (fun (self: t_U16) -> true);
//     f_lift_post = (fun (self: t_U16) (out: Hax_base.Int.t_HaxInt) -> true);
//     f_lift = fun (self: t_U16) -> self.f_v
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_35: Core.Cmp.t_PartialEq t_U16 t_U16 =
//   {
//     f_eq_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_eq_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
//     f_eq
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_base.Int.BaseImpl.impl__eq (Hax_core.Coerce.f_lift #t_U16
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
//           <:
//           Hax_base.Int.t_HaxInt)
//         (Hax_core.Coerce.f_lift #t_U16
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_36: Core.Cmp.t_PartialOrd t_U16 t_U16 =
//   {
//     _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
//     f_partial_cmp_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_partial_cmp_post
//     =
//     (fun (self: t_U16) (rhs: t_U16) (out: // Core.Option.t_Option
//      option Core.Cmp.t_Ordering) -> true);
//     f_partial_cmp
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Core.Option.// Option_Some
//       (match
//           Hax
//           Some _base.Int.BaseImpl.impl__cmp (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
//               <:
//               Hax_base.Int.t_HaxInt)
//         with
//         | Hax_base.Int.CMP_LESS  -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_EQ  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_GREATER  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
//       <:
//       // Core.Option.t_Option
//        option Core.Cmp.t_Ordering
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_55: Hax_core.Coerce.t_Abstraction t_U32 =
//   {
//     f_AbstractType = Hax_base.Int.t_HaxInt;
//     f_lift_pre = (fun (self: t_U32) -> true);
//     f_lift_post = (fun (self: t_U32) (out: Hax_base.Int.t_HaxInt) -> true);
//     f_lift = fun (self: t_U32) -> self.f_v
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_62: Core.Cmp.t_PartialEq t_U32 t_U32 =
//   {
//     f_eq_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_eq_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
//     f_eq
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_base.Int.BaseImpl.impl__eq (Hax_core.Coerce.f_lift #t_U32
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
//           <:
//           Hax_base.Int.t_HaxInt)
//         (Hax_core.Coerce.f_lift #t_U32
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_63: Core.Cmp.t_PartialOrd t_U32 t_U32 =
//   {
//     _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
//     f_partial_cmp_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_partial_cmp_post
//     =
//     (fun (self: t_U32) (rhs: t_U32) (out: // Core.Option.t_Option
//      option Core.Cmp.t_Ordering) -> true);
//     f_partial_cmp
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Core.Option.// Option_Some
//       (match
//           Hax
//           Some _base.Int.BaseImpl.impl__cmp (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
//               <:
//               Hax_base.Int.t_HaxInt)
//         with
//         | Hax_base.Int.CMP_LESS  -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_EQ  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_GREATER  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
//       <:
//       // Core.Option.t_Option
//        option Core.Cmp.t_Ordering
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_82: Hax_core.Coerce.t_Abstraction t_U64 =
//   {
//     f_AbstractType = Hax_base.Int.t_HaxInt;
//     f_lift_pre = (fun (self: t_U64) -> true);
//     f_lift_post = (fun (self: t_U64) (out: Hax_base.Int.t_HaxInt) -> true);
//     f_lift = fun (self: t_U64) -> self.f_v
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_89: Core.Cmp.t_PartialEq t_U64 t_U64 =
//   {
//     f_eq_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_eq_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
//     f_eq
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_base.Int.BaseImpl.impl__eq (Hax_core.Coerce.f_lift #t_U64
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
//           <:
//           Hax_base.Int.t_HaxInt)
//         (Hax_core.Coerce.f_lift #t_U64
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_90: Core.Cmp.t_PartialOrd t_U64 t_U64 =
//   {
//     _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
//     f_partial_cmp_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_partial_cmp_post
//     =
//     (fun (self: t_U64) (rhs: t_U64) (out: // Core.Option.t_Option
//      option Core.Cmp.t_Ordering) -> true);
//     f_partial_cmp
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Core.Option.// Option_Some
//       (match
//           Hax
//           Some _base.Int.BaseImpl.impl__cmp (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
//               <:
//               Hax_base.Int.t_HaxInt)
//         with
//         | Hax_base.Int.CMP_LESS  -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_EQ  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_GREATER  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
//       <:
//       // Core.Option.t_Option
//        option Core.Cmp.t_Ordering
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_109: Hax_core.Coerce.t_Abstraction t_U128 =
//   {
//     f_AbstractType = Hax_base.Int.t_HaxInt;
//     f_lift_pre = (fun (self: t_U128) -> true);
//     f_lift_post = (fun (self: t_U128) (out: Hax_base.Int.t_HaxInt) -> true);
//     f_lift = fun (self: t_U128) -> self.f_v
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_116: Core.Cmp.t_PartialEq t_U128 t_U128 =
//   {
//     f_eq_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_eq_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
//     f_eq
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_base.Int.BaseImpl.impl__eq (Hax_core.Coerce.f_lift #t_U128
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
//           <:
//           Hax_base.Int.t_HaxInt)
//         (Hax_core.Coerce.f_lift #t_U128
//             #FStar.Tactics.Typeclasses.solve
//             (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_117: Core.Cmp.t_PartialOrd t_U128 t_U128 =
//   {
//     _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
//     f_partial_cmp_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_partial_cmp_post
//     =
//     (fun (self: t_U128) (rhs: t_U128) (out: // Core.Option.t_Option
//      option Core.Cmp.t_Ordering) -> true);
//     f_partial_cmp
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       // Core.Option.Option_Some
//       Some 
//       (match
//           Hax_base.Int.BaseImpl.impl__cmp (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
//               <:
//               Hax_base.Int.t_HaxInt)
//         with
//         | Hax_base.Int.CMP_LESS  -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_EQ  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
//         | Hax_base.Int.CMP_GREATER  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
//       <:
//       // Core.Option.t_Option
//        option // Core.Cmp.t_Ordering
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_4: Core.Ops.Arith.t_Neg t_U8 =
//   {
//     f_Output = t_U8;
//     f_neg_pre = (fun (self: t_U8) -> true);
//     f_neg_post = (fun (self: t_U8) (out: t_U8) -> true);
//     f_neg
//     =
//     fun (self: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__sub Hax_base.Int.BaseSpec.v_WORDSIZE_8_
//             (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U8
//                     #FStar.Tactics.Typeclasses.solve
//                     self
//                   <:
//                   Hax_base.Int.t_HaxInt)
//                 Hax_base.Int.BaseSpec.v_WORDSIZE_8_
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_10: Core.Ops.Arith.t_Mul t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_mul_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_mul_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_mul
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__mul (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_11: Core.Ops.Arith.t_Rem t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_rem_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_rem_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_rem
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_12: Core.Ops.Arith.t_Add t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_add_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_add_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_add
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__add (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_13: Core.Ops.Arith.t_Div t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_div_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_div_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_div
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__div (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_14: Core.Ops.Bit.t_Shl t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_shl_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_shl_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_shl
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_15: Core.Ops.Bit.t_Shl t_U8 t_U16 =
//   {
//     f_Output = t_U8;
//     f_shl_pre = (fun (self: t_U8) (rhs: t_U16) -> true);
//     f_shl_post = (fun (self: t_U8) (rhs: t_U16) (out: t_U8) -> true);
//     f_shl
//     =
//     fun (self: t_U8) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_16: Core.Ops.Bit.t_Shl t_U8 t_U32 =
//   {
//     f_Output = t_U8;
//     f_shl_pre = (fun (self: t_U8) (rhs: t_U32) -> true);
//     f_shl_post = (fun (self: t_U8) (rhs: t_U32) (out: t_U8) -> true);
//     f_shl
//     =
//     fun (self: t_U8) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_17: Core.Ops.Bit.t_Shl t_U8 t_U64 =
//   {
//     f_Output = t_U8;
//     f_shl_pre = (fun (self: t_U8) (rhs: t_U64) -> true);
//     f_shl_post = (fun (self: t_U8) (rhs: t_U64) (out: t_U8) -> true);
//     f_shl
//     =
//     fun (self: t_U8) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_18: Core.Ops.Bit.t_Shl t_U8 t_U128 =
//   {
//     f_Output = t_U8;
//     f_shl_pre = (fun (self: t_U8) (rhs: t_U128) -> true);
//     f_shl_post = (fun (self: t_U8) (rhs: t_U128) (out: t_U8) -> true);
//     f_shl
//     =
//     fun (self: t_U8) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_19: Core.Ops.Bit.t_Shr t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_shr_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_shr_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_shr
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_20: Core.Ops.Bit.t_Shr t_U8 t_U16 =
//   {
//     f_Output = t_U8;
//     f_shr_pre = (fun (self: t_U8) (rhs: t_U16) -> true);
//     f_shr_post = (fun (self: t_U8) (rhs: t_U16) (out: t_U8) -> true);
//     f_shr
//     =
//     fun (self: t_U8) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_21: Core.Ops.Bit.t_Shr t_U8 t_U32 =
//   {
//     f_Output = t_U8;
//     f_shr_pre = (fun (self: t_U8) (rhs: t_U32) -> true);
//     f_shr_post = (fun (self: t_U8) (rhs: t_U32) (out: t_U8) -> true);
//     f_shr
//     =
//     fun (self: t_U8) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_22: Core.Ops.Bit.t_Shr t_U8 t_U64 =
//   {
//     f_Output = t_U8;
//     f_shr_pre = (fun (self: t_U8) (rhs: t_U64) -> true);
//     f_shr_post = (fun (self: t_U8) (rhs: t_U64) (out: t_U8) -> true);
//     f_shr
//     =
//     fun (self: t_U8) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_23: Core.Ops.Bit.t_Shr t_U8 t_U128 =
//   {
//     f_Output = t_U8;
//     f_shr_pre = (fun (self: t_U8) (rhs: t_U128) -> true);
//     f_shr_post = (fun (self: t_U8) (rhs: t_U128) (out: t_U8) -> true);
//     f_shr
//     =
//     fun (self: t_U8) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_24: Core.Ops.Bit.t_BitXor t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_bitxor_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_bitxor_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_bitxor
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitxor (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_25: Core.Ops.Bit.t_BitAnd t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_bitand_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_bitand_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_bitand
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitand (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_26: Core.Ops.Bit.t_BitOr t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_bitor_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_bitor_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_bitor
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U8
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitor (Hax_core.Coerce.f_lift #t_U8
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_31: Core.Ops.Arith.t_Neg t_U16 =
//   {
//     f_Output = t_U16;
//     f_neg_pre = (fun (self: t_U16) -> true);
//     f_neg_post = (fun (self: t_U16) (out: t_U16) -> true);
//     f_neg
//     =
//     fun (self: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__sub Hax_base.Int.BaseSpec.v_WORDSIZE_16_
//             (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U16
//                     #FStar.Tactics.Typeclasses.solve
//                     self
//                   <:
//                   Hax_base.Int.t_HaxInt)
//                 Hax_base.Int.BaseSpec.v_WORDSIZE_16_
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_37: Core.Ops.Arith.t_Mul t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_mul_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_mul_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_mul
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__mul (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_38: Core.Ops.Arith.t_Rem t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_rem_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_rem_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_rem
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_39: Core.Ops.Arith.t_Add t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_add_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_add_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_add
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__add (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_40: Core.Ops.Arith.t_Div t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_div_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_div_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_div
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__div (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_41: Core.Ops.Bit.t_Shl t_U16 t_U8 =
//   {
//     f_Output = t_U16;
//     f_shl_pre = (fun (self: t_U16) (rhs: t_U8) -> true);
//     f_shl_post = (fun (self: t_U16) (rhs: t_U8) (out: t_U16) -> true);
//     f_shl
//     =
//     fun (self: t_U16) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_42: Core.Ops.Bit.t_Shl t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_shl_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_shl_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_shl
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_43: Core.Ops.Bit.t_Shl t_U16 t_U32 =
//   {
//     f_Output = t_U16;
//     f_shl_pre = (fun (self: t_U16) (rhs: t_U32) -> true);
//     f_shl_post = (fun (self: t_U16) (rhs: t_U32) (out: t_U16) -> true);
//     f_shl
//     =
//     fun (self: t_U16) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_44: Core.Ops.Bit.t_Shl t_U16 t_U64 =
//   {
//     f_Output = t_U16;
//     f_shl_pre = (fun (self: t_U16) (rhs: t_U64) -> true);
//     f_shl_post = (fun (self: t_U16) (rhs: t_U64) (out: t_U16) -> true);
//     f_shl
//     =
//     fun (self: t_U16) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_45: Core.Ops.Bit.t_Shl t_U16 t_U128 =
//   {
//     f_Output = t_U16;
//     f_shl_pre = (fun (self: t_U16) (rhs: t_U128) -> true);
//     f_shl_post = (fun (self: t_U16) (rhs: t_U128) (out: t_U16) -> true);
//     f_shl
//     =
//     fun (self: t_U16) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_46: Core.Ops.Bit.t_Shr t_U16 t_U8 =
//   {
//     f_Output = t_U16;
//     f_shr_pre = (fun (self: t_U16) (rhs: t_U8) -> true);
//     f_shr_post = (fun (self: t_U16) (rhs: t_U8) (out: t_U16) -> true);
//     f_shr
//     =
//     fun (self: t_U16) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_47: Core.Ops.Bit.t_Shr t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_shr_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_shr_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_shr
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_48: Core.Ops.Bit.t_Shr t_U16 t_U32 =
//   {
//     f_Output = t_U16;
//     f_shr_pre = (fun (self: t_U16) (rhs: t_U32) -> true);
//     f_shr_post = (fun (self: t_U16) (rhs: t_U32) (out: t_U16) -> true);
//     f_shr
//     =
//     fun (self: t_U16) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_49: Core.Ops.Bit.t_Shr t_U16 t_U64 =
//   {
//     f_Output = t_U16;
//     f_shr_pre = (fun (self: t_U16) (rhs: t_U64) -> true);
//     f_shr_post = (fun (self: t_U16) (rhs: t_U64) (out: t_U16) -> true);
//     f_shr
//     =
//     fun (self: t_U16) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_50: Core.Ops.Bit.t_Shr t_U16 t_U128 =
//   {
//     f_Output = t_U16;
//     f_shr_pre = (fun (self: t_U16) (rhs: t_U128) -> true);
//     f_shr_post = (fun (self: t_U16) (rhs: t_U128) (out: t_U16) -> true);
//     f_shr
//     =
//     fun (self: t_U16) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_51: Core.Ops.Bit.t_BitXor t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_bitxor_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_bitxor_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_bitxor
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitxor (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_52: Core.Ops.Bit.t_BitAnd t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_bitand_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_bitand_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_bitand
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitand (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_53: Core.Ops.Bit.t_BitOr t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_bitor_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_bitor_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_bitor
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U16
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitor (Hax_core.Coerce.f_lift #t_U16
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_58: Core.Ops.Arith.t_Neg t_U32 =
//   {
//     f_Output = t_U32;
//     f_neg_pre = (fun (self: t_U32) -> true);
//     f_neg_post = (fun (self: t_U32) (out: t_U32) -> true);
//     f_neg
//     =
//     fun (self: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__sub Hax_base.Int.BaseSpec.v_WORDSIZE_32_
//             (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U32
//                     #FStar.Tactics.Typeclasses.solve
//                     self
//                   <:
//                   Hax_base.Int.t_HaxInt)
//                 Hax_base.Int.BaseSpec.v_WORDSIZE_32_
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_64: Core.Ops.Arith.t_Mul t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_mul_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_mul_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_mul
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__mul (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_65: Core.Ops.Arith.t_Rem t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_rem_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_rem_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_rem
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_66: Core.Ops.Arith.t_Add t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_add_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_add_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_add
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__add (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_67: Core.Ops.Arith.t_Div t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_div_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_div_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_div
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__div (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_68: Core.Ops.Bit.t_Shl t_U32 t_U8 =
//   {
//     f_Output = t_U32;
//     f_shl_pre = (fun (self: t_U32) (rhs: t_U8) -> true);
//     f_shl_post = (fun (self: t_U32) (rhs: t_U8) (out: t_U32) -> true);
//     f_shl
//     =
//     fun (self: t_U32) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_69: Core.Ops.Bit.t_Shl t_U32 t_U16 =
//   {
//     f_Output = t_U32;
//     f_shl_pre = (fun (self: t_U32) (rhs: t_U16) -> true);
//     f_shl_post = (fun (self: t_U32) (rhs: t_U16) (out: t_U32) -> true);
//     f_shl
//     =
//     fun (self: t_U32) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_70: Core.Ops.Bit.t_Shl t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_shl_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_shl_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_shl
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_71: Core.Ops.Bit.t_Shl t_U32 t_U64 =
//   {
//     f_Output = t_U32;
//     f_shl_pre = (fun (self: t_U32) (rhs: t_U64) -> true);
//     f_shl_post = (fun (self: t_U32) (rhs: t_U64) (out: t_U32) -> true);
//     f_shl
//     =
//     fun (self: t_U32) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_72: Core.Ops.Bit.t_Shl t_U32 t_U128 =
//   {
//     f_Output = t_U32;
//     f_shl_pre = (fun (self: t_U32) (rhs: t_U128) -> true);
//     f_shl_post = (fun (self: t_U32) (rhs: t_U128) (out: t_U32) -> true);
//     f_shl
//     =
//     fun (self: t_U32) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_73: Core.Ops.Bit.t_Shr t_U32 t_U8 =
//   {
//     f_Output = t_U32;
//     f_shr_pre = (fun (self: t_U32) (rhs: t_U8) -> true);
//     f_shr_post = (fun (self: t_U32) (rhs: t_U8) (out: t_U32) -> true);
//     f_shr
//     =
//     fun (self: t_U32) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_74: Core.Ops.Bit.t_Shr t_U32 t_U16 =
//   {
//     f_Output = t_U32;
//     f_shr_pre = (fun (self: t_U32) (rhs: t_U16) -> true);
//     f_shr_post = (fun (self: t_U32) (rhs: t_U16) (out: t_U32) -> true);
//     f_shr
//     =
//     fun (self: t_U32) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_75: Core.Ops.Bit.t_Shr t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_shr_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_shr_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_shr
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_76: Core.Ops.Bit.t_Shr t_U32 t_U64 =
//   {
//     f_Output = t_U32;
//     f_shr_pre = (fun (self: t_U32) (rhs: t_U64) -> true);
//     f_shr_post = (fun (self: t_U32) (rhs: t_U64) (out: t_U32) -> true);
//     f_shr
//     =
//     fun (self: t_U32) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_77: Core.Ops.Bit.t_Shr t_U32 t_U128 =
//   {
//     f_Output = t_U32;
//     f_shr_pre = (fun (self: t_U32) (rhs: t_U128) -> true);
//     f_shr_post = (fun (self: t_U32) (rhs: t_U128) (out: t_U32) -> true);
//     f_shr
//     =
//     fun (self: t_U32) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_78: Core.Ops.Bit.t_BitXor t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_bitxor_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_bitxor_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_bitxor
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitxor (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_79: Core.Ops.Bit.t_BitAnd t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_bitand_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_bitand_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_bitand
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitand (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_80: Core.Ops.Bit.t_BitOr t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_bitor_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_bitor_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_bitor
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U32
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitor (Hax_core.Coerce.f_lift #t_U32
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_85: Core.Ops.Arith.t_Neg t_U64 =
//   {
//     f_Output = t_U64;
//     f_neg_pre = (fun (self: t_U64) -> true);
//     f_neg_post = (fun (self: t_U64) (out: t_U64) -> true);
//     f_neg
//     =
//     fun (self: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__sub Hax_base.Int.BaseSpec.v_WORDSIZE_64_
//             (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U64
//                     #FStar.Tactics.Typeclasses.solve
//                     self
//                   <:
//                   Hax_base.Int.t_HaxInt)
//                 Hax_base.Int.BaseSpec.v_WORDSIZE_64_
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_91: Core.Ops.Arith.t_Mul t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_mul_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_mul_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_mul
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__mul (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_92: Core.Ops.Arith.t_Rem t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_rem_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_rem_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_rem
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_93: Core.Ops.Arith.t_Add t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_add_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_add_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_add
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__add (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_94: Core.Ops.Arith.t_Div t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_div_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_div_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_div
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__div (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_95: Core.Ops.Bit.t_Shl t_U64 t_U8 =
//   {
//     f_Output = t_U64;
//     f_shl_pre = (fun (self: t_U64) (rhs: t_U8) -> true);
//     f_shl_post = (fun (self: t_U64) (rhs: t_U8) (out: t_U64) -> true);
//     f_shl
//     =
//     fun (self: t_U64) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_96: Core.Ops.Bit.t_Shl t_U64 t_U16 =
//   {
//     f_Output = t_U64;
//     f_shl_pre = (fun (self: t_U64) (rhs: t_U16) -> true);
//     f_shl_post = (fun (self: t_U64) (rhs: t_U16) (out: t_U64) -> true);
//     f_shl
//     =
//     fun (self: t_U64) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_97: Core.Ops.Bit.t_Shl t_U64 t_U32 =
//   {
//     f_Output = t_U64;
//     f_shl_pre = (fun (self: t_U64) (rhs: t_U32) -> true);
//     f_shl_post = (fun (self: t_U64) (rhs: t_U32) (out: t_U64) -> true);
//     f_shl
//     =
//     fun (self: t_U64) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_98: Core.Ops.Bit.t_Shl t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_shl_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_shl_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_shl
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_99: Core.Ops.Bit.t_Shl t_U64 t_U128 =
//   {
//     f_Output = t_U64;
//     f_shl_pre = (fun (self: t_U64) (rhs: t_U128) -> true);
//     f_shl_post = (fun (self: t_U64) (rhs: t_U128) (out: t_U64) -> true);
//     f_shl
//     =
//     fun (self: t_U64) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_100: Core.Ops.Bit.t_Shr t_U64 t_U8 =
//   {
//     f_Output = t_U64;
//     f_shr_pre = (fun (self: t_U64) (rhs: t_U8) -> true);
//     f_shr_post = (fun (self: t_U64) (rhs: t_U8) (out: t_U64) -> true);
//     f_shr
//     =
//     fun (self: t_U64) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_101: Core.Ops.Bit.t_Shr t_U64 t_U16 =
//   {
//     f_Output = t_U64;
//     f_shr_pre = (fun (self: t_U64) (rhs: t_U16) -> true);
//     f_shr_post = (fun (self: t_U64) (rhs: t_U16) (out: t_U64) -> true);
//     f_shr
//     =
//     fun (self: t_U64) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_102: Core.Ops.Bit.t_Shr t_U64 t_U32 =
//   {
//     f_Output = t_U64;
//     f_shr_pre = (fun (self: t_U64) (rhs: t_U32) -> true);
//     f_shr_post = (fun (self: t_U64) (rhs: t_U32) (out: t_U64) -> true);
//     f_shr
//     =
//     fun (self: t_U64) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_103: Core.Ops.Bit.t_Shr t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_shr_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_shr_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_shr
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_104: Core.Ops.Bit.t_Shr t_U64 t_U128 =
//   {
//     f_Output = t_U64;
//     f_shr_pre = (fun (self: t_U64) (rhs: t_U128) -> true);
//     f_shr_post = (fun (self: t_U64) (rhs: t_U128) (out: t_U64) -> true);
//     f_shr
//     =
//     fun (self: t_U64) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_105: Core.Ops.Bit.t_BitXor t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_bitxor_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_bitxor_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_bitxor
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitxor (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_106: Core.Ops.Bit.t_BitAnd t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_bitand_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_bitand_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_bitand
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitand (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_107: Core.Ops.Bit.t_BitOr t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_bitor_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_bitor_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_bitor
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U64
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitor (Hax_core.Coerce.f_lift #t_U64
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_112: Core.Ops.Arith.t_Neg t_U128 =
//   {
//     f_Output = t_U128;
//     f_neg_pre = (fun (self: t_U128) -> true);
//     f_neg_post = (fun (self: t_U128) (out: t_U128) -> true);
//     f_neg
//     =
//     fun (self: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__sub Hax_base.Int.BaseSpec.v_WORDSIZE_128_
//             (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U128
//                     #FStar.Tactics.Typeclasses.solve
//                     self
//                   <:
//                   Hax_base.Int.t_HaxInt)
//                 Hax_base.Int.BaseSpec.v_WORDSIZE_128_
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_118: Core.Ops.Arith.t_Mul t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_mul_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_mul_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_mul
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__mul (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_119: Core.Ops.Arith.t_Rem t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_rem_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_rem_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_rem
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__rem (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_120: Core.Ops.Arith.t_Add t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_add_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_add_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_add
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__add (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_121: Core.Ops.Arith.t_Div t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_div_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_div_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_div
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__div (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_122: Core.Ops.Bit.t_Shl t_U128 t_U8 =
//   {
//     f_Output = t_U128;
//     f_shl_pre = (fun (self: t_U128) (rhs: t_U8) -> true);
//     f_shl_post = (fun (self: t_U128) (rhs: t_U8) (out: t_U128) -> true);
//     f_shl
//     =
//     fun (self: t_U128) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_123: Core.Ops.Bit.t_Shl t_U128 t_U16 =
//   {
//     f_Output = t_U128;
//     f_shl_pre = (fun (self: t_U128) (rhs: t_U16) -> true);
//     f_shl_post = (fun (self: t_U128) (rhs: t_U16) (out: t_U128) -> true);
//     f_shl
//     =
//     fun (self: t_U128) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_124: Core.Ops.Bit.t_Shl t_U128 t_U32 =
//   {
//     f_Output = t_U128;
//     f_shl_pre = (fun (self: t_U128) (rhs: t_U32) -> true);
//     f_shl_post = (fun (self: t_U128) (rhs: t_U32) (out: t_U128) -> true);
//     f_shl
//     =
//     fun (self: t_U128) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_125: Core.Ops.Bit.t_Shl t_U128 t_U64 =
//   {
//     f_Output = t_U128;
//     f_shl_pre = (fun (self: t_U128) (rhs: t_U64) -> true);
//     f_shl_post = (fun (self: t_U128) (rhs: t_U64) (out: t_U128) -> true);
//     f_shl
//     =
//     fun (self: t_U128) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_126: Core.Ops.Bit.t_Shl t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_shl_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_shl_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_shl
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shl (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_127: Core.Ops.Bit.t_Shr t_U128 t_U8 =
//   {
//     f_Output = t_U128;
//     f_shr_pre = (fun (self: t_U128) (rhs: t_U8) -> true);
//     f_shr_post = (fun (self: t_U128) (rhs: t_U8) (out: t_U128) -> true);
//     f_shr
//     =
//     fun (self: t_U128) (rhs: t_U8) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_128: Core.Ops.Bit.t_Shr t_U128 t_U16 =
//   {
//     f_Output = t_U128;
//     f_shr_pre = (fun (self: t_U128) (rhs: t_U16) -> true);
//     f_shr_post = (fun (self: t_U128) (rhs: t_U16) (out: t_U128) -> true);
//     f_shr
//     =
//     fun (self: t_U128) (rhs: t_U16) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_129: Core.Ops.Bit.t_Shr t_U128 t_U32 =
//   {
//     f_Output = t_U128;
//     f_shr_pre = (fun (self: t_U128) (rhs: t_U32) -> true);
//     f_shr_post = (fun (self: t_U128) (rhs: t_U32) (out: t_U128) -> true);
//     f_shr
//     =
//     fun (self: t_U128) (rhs: t_U32) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_130: Core.Ops.Bit.t_Shr t_U128 t_U64 =
//   {
//     f_Output = t_U128;
//     f_shr_pre = (fun (self: t_U128) (rhs: t_U64) -> true);
//     f_shr_post = (fun (self: t_U128) (rhs: t_U64) (out: t_U128) -> true);
//     f_shr
//     =
//     fun (self: t_U128) (rhs: t_U64) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_131: Core.Ops.Bit.t_Shr t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_shr_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_shr_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_shr
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__shr (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_132: Core.Ops.Bit.t_BitXor t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_bitxor_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_bitxor_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_bitxor
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitxor (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_133: Core.Ops.Bit.t_BitAnd t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_bitand_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_bitand_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_bitand
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitand (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_134: Core.Ops.Bit.t_BitOr t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_bitor_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_bitor_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_bitor
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       Hax_core.Coerce.f_concretize #Hax_base.Int.t_HaxInt
//         #t_U128
//         #FStar.Tactics.Typeclasses.solve
//         (Hax_base.Int.BaseImpl.impl__bitor (Hax_core.Coerce.f_lift #t_U128
//                 #FStar.Tactics.Typeclasses.solve
//                 self
//               <:
//               Hax_base.Int.t_HaxInt)
//             (Hax_core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
//               <:
//               Hax_base.Int.t_HaxInt)
//           <:
//           Hax_base.Int.t_HaxInt)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_5: Core.Ops.Arith.t_Sub t_U8 t_U8 =
//   {
//     f_Output = t_U8;
//     f_sub_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
//     f_sub_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
//     f_sub
//     =
//     fun (self: t_U8) (rhs: t_U8) ->
//       self +! (Core.Ops.Arith.f_neg #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_6: Core.Ops.Bit.t_Not t_U8 =
//   {
//     f_Output = t_U8;
//     f_not_pre = (fun (self: t_U8) -> true);
//     f_not_post = (fun (self: t_U8) (out: t_U8) -> true);
//     f_not = fun (self: t_U8) -> self ^. Hax_core.Num.impl__MAX
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_32: Core.Ops.Arith.t_Sub t_U16 t_U16 =
//   {
//     f_Output = t_U16;
//     f_sub_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
//     f_sub_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
//     f_sub
//     =
//     fun (self: t_U16) (rhs: t_U16) ->
//       self +! (Core.Ops.Arith.f_neg #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_33: Core.Ops.Bit.t_Not t_U16 =
//   {
//     f_Output = t_U16;
//     f_not_pre = (fun (self: t_U16) -> true);
//     f_not_post = (fun (self: t_U16) (out: t_U16) -> true);
//     f_not = fun (self: t_U16) -> self ^. f_MAX
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_59: Core.Ops.Arith.t_Sub t_U32 t_U32 =
//   {
//     f_Output = t_U32;
//     f_sub_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
//     f_sub_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
//     f_sub
//     =
//     fun (self: t_U32) (rhs: t_U32) ->
//       self +! (Core.Ops.Arith.f_neg #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_60: Core.Ops.Bit.t_Not t_U32 =
//   {
//     f_Output = t_U32;
//     f_not_pre = (fun (self: t_U32) -> true);
//     f_not_post = (fun (self: t_U32) (out: t_U32) -> true);
//     f_not = fun (self: t_U32) -> self ^. f_MAX
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_86: Core.Ops.Arith.t_Sub t_U64 t_U64 =
//   {
//     f_Output = t_U64;
//     f_sub_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
//     f_sub_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
//     f_sub
//     =
//     fun (self: t_U64) (rhs: t_U64) ->
//       self +! (Core.Ops.Arith.f_neg #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_87: Core.Ops.Bit.t_Not t_U64 =
//   {
//     f_Output = t_U64;
//     f_not_pre = (fun (self: t_U64) -> true);
//     f_not_post = (fun (self: t_U64) (out: t_U64) -> true);
//     f_not = fun (self: t_U64) -> self ^. f_MAX
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_113: Core.Ops.Arith.t_Sub t_U128 t_U128 =
//   {
//     f_Output = t_U128;
//     f_sub_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
//     f_sub_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
//     f_sub
//     =
//     fun (self: t_U128) (rhs: t_U128) ->
//       self +! (Core.Ops.Arith.f_neg #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
//   }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_114: Core.Ops.Bit.t_Not t_U128 =
//   {
//     f_Output = t_U128;
//     f_not_pre = (fun (self: t_U128) -> true);
//     f_not_post = (fun (self: t_U128) (out: t_U128) -> true);
//     f_not = fun (self: t_U128) -> self ^. f_MAX
//   }
