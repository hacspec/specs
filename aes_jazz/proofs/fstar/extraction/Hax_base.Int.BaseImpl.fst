module Hax_base.Int.BaseImpl
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
// open Core
open FStar.Mul

let impl__double (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POS_POS p -> Hax_base.Int.BaseSpec.impl_1__xO p

let impl__double_mask (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POS_POS p -> Hax_base.Int.BaseSpec.impl_1__xO p

let impl__succ_double (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_1__xH
  | Hax_base.Int.POS_POS p -> Hax_base.Int.BaseSpec.impl_1__xI p

let impl__succ_double_mask (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_1__xH
  | Hax_base.Int.POS_POS p -> Hax_base.Int.BaseSpec.impl_1__xI p

let impl__half (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POS_POS n ->
    match Hax_base.Int.BaseSpec.impl_1__match_positive n with
    | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_2__ZERO
    | Hax_base.Int.POSITIVE_XO p -> p
    | Hax_base.Int.POSITIVE_XI p -> p

let rec impl__add_binary (self rhs: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero rhs <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
      | Hax_base.Int.POSITIVE_XH  ->
        Hax_base.Int.BaseSpec.impl_1__xO Hax_base.Int.BaseSpec.impl_1__xH
      | Hax_base.Int.POSITIVE_XO q -> Hax_base.Int.BaseSpec.impl_1__xI q
      | Hax_base.Int.POSITIVE_XI q ->
        Hax_base.Int.BaseSpec.impl_1__xO (Hax_base.Int.BaseSpec.impl_2__succ q
            <:
            Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XO p ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
      | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_1__xI p
      | Hax_base.Int.POSITIVE_XO q ->
        Hax_base.Int.BaseSpec.impl_1__xO (impl__add_binary p q <: Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XI q ->
        Hax_base.Int.BaseSpec.impl_1__xI (impl__add_binary p q <: Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XI p ->
    match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
    | Hax_base.Int.POSITIVE_XH  ->
      Hax_base.Int.BaseSpec.impl_1__xO (Hax_base.Int.BaseSpec.impl_2__succ p
          <:
          Hax_base.Int.t_HaxInt)
    | Hax_base.Int.POSITIVE_XO q ->
      Hax_base.Int.BaseSpec.impl_1__xI (impl__add_binary p q <: Hax_base.Int.t_HaxInt)
    | Hax_base.Int.POSITIVE_XI q ->
      Hax_base.Int.BaseSpec.impl_1__xO (impl__add_carry p q <: Hax_base.Int.t_HaxInt)

and impl__add_carry (self rhs: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero rhs <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
      | Hax_base.Int.POSITIVE_XH  ->
        Hax_base.Int.BaseSpec.impl_1__xI Hax_base.Int.BaseSpec.impl_1__xH
      | Hax_base.Int.POSITIVE_XO q ->
        Hax_base.Int.BaseSpec.impl_1__xO (Hax_base.Int.BaseSpec.impl_2__succ q
            <:
            Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XI q ->
        Hax_base.Int.BaseSpec.impl_1__xI (Hax_base.Int.BaseSpec.impl_2__succ q
            <:
            Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XO p ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
      | Hax_base.Int.POSITIVE_XH  ->
        Hax_base.Int.BaseSpec.impl_1__xO (Hax_base.Int.BaseSpec.impl_2__succ p
            <:
            Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XO q ->
        Hax_base.Int.BaseSpec.impl_1__xI (impl__add_binary p q <: Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XI q ->
        Hax_base.Int.BaseSpec.impl_1__xO (impl__add_carry p q <: Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XI p ->
    match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
    | Hax_base.Int.POSITIVE_XH  ->
      Hax_base.Int.BaseSpec.impl_1__xI (Hax_base.Int.BaseSpec.impl_2__succ p
          <:
          Hax_base.Int.t_HaxInt)
    | Hax_base.Int.POSITIVE_XO q ->
      Hax_base.Int.BaseSpec.impl_1__xO (impl__add_carry p q <: Hax_base.Int.t_HaxInt)
    | Hax_base.Int.POSITIVE_XI q ->
      Hax_base.Int.BaseSpec.impl_1__xI (impl__add_carry p q <: Hax_base.Int.t_HaxInt)

let impl__add (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> rhs
  | Hax_base.Int.POS_POS p ->
    match Hax_base.Int.BaseSpec.impl_1__match_pos rhs with
    | Hax_base.Int.POS_ZERO  -> p
    | Hax_base.Int.POS_POS q -> impl__add_binary p q

let rec impl__add_unary (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match
    Hax_base.Int.BaseSpec.impl_2__match_unary (Hax_base.Int.BaseSpec.impl__clone self
        <:
        Hax_base.Int.t_HaxInt)
  with
  | Hax_base.Int.UNARY_ZERO  ->
    let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc self in
    Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.UNARY_SUCC x ->
    impl__add_unary x (Hax_base.Int.BaseSpec.impl_2__succ rhs <: Hax_base.Int.t_HaxInt)

let rec impl__cmp_binary_cont (x y: Hax_base.Int.t_HaxInt) (r: Hax_base.Int.t_CMP)
    : Prims.Pure Hax_base.Int.t_CMP
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero x <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero y <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive x with
  | Hax_base.Int.POSITIVE_XH  ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive y with
      | Hax_base.Int.POSITIVE_XH  -> r
      | Hax_base.Int.POSITIVE_XO q
      | Hax_base.Int.POSITIVE_XI q ->
        let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc q in
        Hax_base.Int.CMP_LESS <: Hax_base.Int.t_CMP)
  | Hax_base.Int.POSITIVE_XO p ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive y with
      | Hax_base.Int.POSITIVE_XH  ->
        let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc p in
        Hax_base.Int.CMP_GREATER <: Hax_base.Int.t_CMP
      | Hax_base.Int.POSITIVE_XO q -> impl__cmp_binary_cont p q r
      | Hax_base.Int.POSITIVE_XI q ->
        impl__cmp_binary_cont p q (Hax_base.Int.CMP_LESS <: Hax_base.Int.t_CMP))
  | Hax_base.Int.POSITIVE_XI p ->
    match Hax_base.Int.BaseSpec.impl_1__match_positive y with
    | Hax_base.Int.POSITIVE_XH  ->
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc p in
      Hax_base.Int.CMP_GREATER <: Hax_base.Int.t_CMP
    | Hax_base.Int.POSITIVE_XO q ->
      impl__cmp_binary_cont p q (Hax_base.Int.CMP_GREATER <: Hax_base.Int.t_CMP)
    | Hax_base.Int.POSITIVE_XI q -> impl__cmp_binary_cont p q r

let impl__cmp_binary (self rhs: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_CMP
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero rhs <: bool))
      (fun _ -> Prims.l_True) =
  impl__cmp_binary_cont self rhs (Hax_base.Int.CMP_EQ <: Hax_base.Int.t_CMP)

let impl__cmp (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_CMP =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  ->
    (match Hax_base.Int.BaseSpec.impl_1__match_pos rhs with
      | Hax_base.Int.POS_ZERO  -> Hax_base.Int.CMP_EQ <: Hax_base.Int.t_CMP
      | Hax_base.Int.POS_POS q ->
        let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc q in
        Hax_base.Int.CMP_LESS <: Hax_base.Int.t_CMP)
  | Hax_base.Int.POS_POS p ->
    match Hax_base.Int.BaseSpec.impl_1__match_pos rhs with
    | Hax_base.Int.POS_ZERO  ->
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc p in
      Hax_base.Int.CMP_GREATER <: Hax_base.Int.t_CMP
    | Hax_base.Int.POS_POS q -> impl__cmp_binary p q

let impl__cmp_unary (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_CMP =
  if
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone self
        <:
        Hax_base.Int.t_HaxInt) ||
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone rhs
        <:
        Hax_base.Int.t_HaxInt)
  then
    if
      Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone self
          <:
          Hax_base.Int.t_HaxInt) &&
      Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone rhs
          <:
          Hax_base.Int.t_HaxInt)
    then
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc self in
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc rhs in
      Hax_base.Int.CMP_EQ <: Hax_base.Int.t_CMP
    else
      if Hax_base.Int.BaseSpec.impl_2__is_zero self
      then
        let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc rhs in
        Hax_base.Int.CMP_LESS <: Hax_base.Int.t_CMP
      else
        let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc rhs in
        Hax_base.Int.CMP_GREATER <: Hax_base.Int.t_CMP
  else
    impl__cmp (Hax_base.Int.BaseSpec.impl_2__pred self <: Hax_base.Int.t_HaxInt)
      (Hax_base.Int.BaseSpec.impl_2__pred rhs <: Hax_base.Int.t_HaxInt)

let rec impl__divmod_unary (x y q u: Hax_base.Int.t_HaxInt)
    : (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt) =
  if
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone x
        <:
        Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc x in
    q, u <: (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
  else
    if
      Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone u
          <:
          Hax_base.Int.t_HaxInt)
    then
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc u in
      impl__divmod_unary (Hax_base.Int.BaseSpec.impl_2__pred x <: Hax_base.Int.t_HaxInt)
        (Hax_base.Int.BaseSpec.impl__clone y <: Hax_base.Int.t_HaxInt)
        (Hax_base.Int.BaseSpec.impl_2__succ q <: Hax_base.Int.t_HaxInt)
        y
    else
      impl__divmod_unary (Hax_base.Int.BaseSpec.impl_2__pred x <: Hax_base.Int.t_HaxInt)
        y
        (Hax_base.Int.BaseSpec.impl_2__succ q <: Hax_base.Int.t_HaxInt)
        (Hax_base.Int.BaseSpec.impl_2__pred u <: Hax_base.Int.t_HaxInt)

let impl__eq (self rhs: Hax_base.Int.t_HaxInt) : bool =
  Hax_base.Int.impl__CMP__eq (impl__cmp self rhs <: Hax_base.Int.t_CMP)
    (Hax_base.Int.CMP_EQ <: Hax_base.Int.t_CMP)

let impl__gt (self rhs: Hax_base.Int.t_HaxInt) : bool =
  Hax_base.Int.impl__CMP__eq (impl__cmp self rhs <: Hax_base.Int.t_CMP)
    (Hax_base.Int.CMP_GREATER <: Hax_base.Int.t_CMP)

let impl__le (self rhs: Hax_base.Int.t_HaxInt) : bool = not (impl__gt self rhs <: bool)

let impl__lt (self rhs: Hax_base.Int.t_HaxInt) : bool =
  Hax_base.Int.impl__CMP__eq (impl__cmp self rhs <: Hax_base.Int.t_CMP)
    (Hax_base.Int.CMP_LESS <: Hax_base.Int.t_CMP)

let impl__ge (self rhs: Hax_base.Int.t_HaxInt) : bool = not (impl__lt self rhs <: bool)

let rec impl__power_of_two (self: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_2__match_unary self with
  | Hax_base.Int.UNARY_ZERO  -> Hax_base.Int.BaseSpec.impl_1__xH
  | Hax_base.Int.UNARY_SUCC x ->
    Hax_base.Int.BaseSpec.impl_1__xO (impl__power_of_two x <: Hax_base.Int.t_HaxInt)

let rec impl__pred_double (self: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_1__xH
  | Hax_base.Int.POSITIVE_XO p ->
    Hax_base.Int.BaseSpec.impl_1__xI (impl__pred_double p <: Hax_base.Int.t_HaxInt)
  | Hax_base.Int.POSITIVE_XI p ->
    Hax_base.Int.BaseSpec.impl_1__xI (Hax_base.Int.BaseSpec.impl_1__xO p <: Hax_base.Int.t_HaxInt)

let impl__double_pred_mask (self: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POSITIVE_XO p ->
    Hax_base.Int.BaseSpec.impl_1__xO (impl__pred_double p <: Hax_base.Int.t_HaxInt)
  | Hax_base.Int.POSITIVE_XI p ->
    Hax_base.Int.BaseSpec.impl_1__xO (Hax_base.Int.BaseSpec.impl_1__xO p <: Hax_base.Int.t_HaxInt)

let rec impl__shl_helper (rhs lhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  if
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone lhs
        <:
        Hax_base.Int.t_HaxInt) ||
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone rhs
        <:
        Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc rhs in
    lhs
  else
    impl__shl_helper (Hax_base.Int.BaseSpec.impl_2__pred rhs <: Hax_base.Int.t_HaxInt)
      (impl__double lhs <: Hax_base.Int.t_HaxInt)

let impl__shl (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = impl__shl_helper rhs self

let rec impl__shr_helper (rhs lhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  if
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone lhs
        <:
        Hax_base.Int.t_HaxInt) ||
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone rhs
        <:
        Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc rhs in
    lhs
  else
    impl__shr_helper (Hax_base.Int.BaseSpec.impl_2__pred rhs <: Hax_base.Int.t_HaxInt)
      (impl__half lhs <: Hax_base.Int.t_HaxInt)

let impl__shr (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt = impl__shr_helper rhs self

let rec impl__sub_unary (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_2__match_unary self with
  | Hax_base.Int.UNARY_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.UNARY_SUCC n ->
    match Hax_base.Int.BaseSpec.impl_2__match_unary rhs with
    | Hax_base.Int.UNARY_ZERO  -> Hax_base.Int.BaseSpec.impl_2__succ n
    | Hax_base.Int.UNARY_SUCC m -> impl__sub_unary n m

let rec impl__mul_binary (self rhs: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero rhs <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  -> rhs
  | Hax_base.Int.POSITIVE_XO p ->
    Hax_base.Int.BaseSpec.impl_1__xO (impl__mul_binary p rhs <: Hax_base.Int.t_HaxInt)
  | Hax_base.Int.POSITIVE_XI p ->
    impl__add (Hax_base.Int.BaseSpec.impl__clone rhs <: Hax_base.Int.t_HaxInt)
      (Hax_base.Int.BaseSpec.impl_1__xO (impl__mul_binary p rhs <: Hax_base.Int.t_HaxInt)
        <:
        Hax_base.Int.t_HaxInt)

let impl__mul (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POS_POS p ->
    match Hax_base.Int.BaseSpec.impl_1__match_pos rhs with
    | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
    | Hax_base.Int.POS_POS q -> impl__mul_binary p q

let rec impl__sub_binary (self rhs: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero rhs <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POSITIVE_XO p ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
      | Hax_base.Int.POSITIVE_XH  -> impl__pred_double p
      | Hax_base.Int.POSITIVE_XO q ->
        impl__double_mask (impl__sub_binary p q <: Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XI q ->
        impl__succ_double_mask (impl__sub_carry p q <: Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XI p ->
    match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
    | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_1__xO p
    | Hax_base.Int.POSITIVE_XO q ->
      impl__succ_double_mask (impl__sub_binary p q <: Hax_base.Int.t_HaxInt)
    | Hax_base.Int.POSITIVE_XI q ->
      impl__double_mask (impl__sub_binary p q <: Hax_base.Int.t_HaxInt)

and impl__sub_carry (self rhs: Hax_base.Int.t_HaxInt)
    : Prims.Pure Hax_base.Int.t_HaxInt
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero self <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero rhs <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive self with
  | Hax_base.Int.POSITIVE_XH  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POSITIVE_XO p ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
      | Hax_base.Int.POSITIVE_XH  -> impl__double_pred_mask p
      | Hax_base.Int.POSITIVE_XO q ->
        impl__succ_double_mask (impl__sub_carry p q <: Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XI q ->
        impl__double_mask (impl__sub_carry p q <: Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XI p ->
    match Hax_base.Int.BaseSpec.impl_1__match_positive rhs with
    | Hax_base.Int.POSITIVE_XH  -> impl__pred_double p
    | Hax_base.Int.POSITIVE_XO q ->
      impl__double_mask (impl__sub_binary p q <: Hax_base.Int.t_HaxInt)
    | Hax_base.Int.POSITIVE_XI q ->
      impl__succ_double_mask (impl__sub_carry p q <: Hax_base.Int.t_HaxInt)

let impl__sub (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  match Hax_base.Int.BaseSpec.impl_1__match_pos self with
  | Hax_base.Int.POS_ZERO  -> Hax_base.Int.BaseSpec.impl_2__ZERO
  | Hax_base.Int.POS_POS p ->
    match Hax_base.Int.BaseSpec.impl_1__match_pos rhs with
    | Hax_base.Int.POS_ZERO  -> p
    | Hax_base.Int.POS_POS q -> impl__sub_binary p q

let rec impl__divmod_binary (a b: Hax_base.Int.t_HaxInt)
    : Prims.Pure (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
      (requires
        not (Hax_base.Int.BaseSpec.impl_2__is_zero a <: bool) &&
        not (Hax_base.Int.BaseSpec.impl_2__is_zero b <: bool))
      (fun _ -> Prims.l_True) =
  match Hax_base.Int.BaseSpec.impl_1__match_positive a with
  | Hax_base.Int.POSITIVE_XH  ->
    (match Hax_base.Int.BaseSpec.impl_1__match_positive b with
      | Hax_base.Int.POSITIVE_XH  ->
        Hax_base.Int.BaseSpec.impl_1__xH, Hax_base.Int.BaseSpec.impl_2__ZERO
        <:
        (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
      | Hax_base.Int.POSITIVE_XO q
      | Hax_base.Int.POSITIVE_XI q ->
        let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc q in
        Hax_base.Int.BaseSpec.impl_2__ZERO, Hax_base.Int.BaseSpec.impl_1__xH
        <:
        (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt))
  | Hax_base.Int.POSITIVE_XO a___ ->
    let q, r:(Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt) =
      impl__divmod_binary a___ (Hax_base.Int.BaseSpec.impl__clone b <: Hax_base.Int.t_HaxInt)
    in
    let r___:Hax_base.Int.t_HaxInt = impl__double r in
    if
      impl__le (Hax_base.Int.BaseSpec.impl__clone b <: Hax_base.Int.t_HaxInt)
        (Hax_base.Int.BaseSpec.impl__clone r___ <: Hax_base.Int.t_HaxInt)
    then impl__succ_double q, impl__sub r___ b <: (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
    else
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc b in
      impl__double q, r___ <: (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
  | Hax_base.Int.POSITIVE_XI a___ ->
    let q, r:(Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt) =
      impl__divmod_binary a___ (Hax_base.Int.BaseSpec.impl__clone b <: Hax_base.Int.t_HaxInt)
    in
    let r___:Hax_base.Int.t_HaxInt = impl__succ_double r in
    if
      impl__le (Hax_base.Int.BaseSpec.impl__clone b <: Hax_base.Int.t_HaxInt)
        (Hax_base.Int.BaseSpec.impl__clone r___ <: Hax_base.Int.t_HaxInt)
    then impl__succ_double q, impl__sub r___ b <: (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
    else
      let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc b in
      impl__double q, r___ <: (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)

let impl__divmod (a b: Hax_base.Int.t_HaxInt) : (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt) =
  if
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone a
        <:
        Hax_base.Int.t_HaxInt) ||
    Hax_base.Int.BaseSpec.impl_2__is_zero (Hax_base.Int.BaseSpec.impl__clone b
        <:
        Hax_base.Int.t_HaxInt)
  then
    let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc b in
    Hax_base.Int.BaseSpec.impl_2__ZERO, a <: (Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt)
  else impl__divmod_binary a b

let impl__div (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  let q, r:(Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt) = impl__divmod self rhs in
  let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc r in
  q

let impl__rem (self rhs: Hax_base.Int.t_HaxInt) : Hax_base.Int.t_HaxInt =
  let q, r:(Hax_base.Int.t_HaxInt & Hax_base.Int.t_HaxInt) = impl__divmod self rhs in
  let _:Prims.unit = Hax_base.Int.BaseSpec.impl__dealloc q in
  r

