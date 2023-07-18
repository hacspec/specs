module Hacspec_ovn.Schnorr.Random_oracle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let random_oracle_init (_: Prims.unit) : Prims.unit = ()

type t_QueryCanvas = {
  f_b:array u8 48sz;
  f_sign:Num_bigint.Bigint.t_Sign;
  f_signed:bool
}

let max_under_impl_16: Core.Ops.Arith.Sub.t_Output =
  ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. 384l <: Core.Ops.Bit.Shl.t_Output) -.
  (Num_traits.Identities.One.one <: Num_bigint.Bigint.t_BigInt)

let max_value_under_impl_16: t_QueryCanvas =
  Core.Convert.From.from (max_under_impl_16 <: Num_bigint.Bigint.t_BigInt)

let hex_string_to_bytes_under_impl_16 (s: string) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let s:Alloc.String.t_String =
    if ((Core.Str.len_under_impl s <: usize) %. 2sz <: usize) <>. 0sz
    then
      let x:Alloc.String.t_String = Alloc.String.ToString.to_string "0" in
      let x:Alloc.String.t_String = Alloc.String.push_str_under_impl x s in
      x
    else Alloc.String.ToString.to_string s
  in
  let _:Prims.unit =
    if ~.(((Alloc.String.len_under_impl s <: usize) %. 2sz <: usize) =. 0sz <: bool)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["length of hex string "; ": "] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [
                            Core.Fmt.Rt.new_display_under_impl_1 s <: Core.Fmt.Rt.t_Argument;
                            Core.Fmt.Rt.new_display_under_impl_1 (Alloc.String.len_under_impl s
                                <:
                                usize)
                            <:
                            Core.Fmt.Rt.t_Argument
                          ]
                        in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let
  (b: Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Core.Num.Error.t_ParseIntError):Core.Result.t_Result
    (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Core.Num.Error.t_ParseIntError =
    Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end = Alloc.String.len_under_impl s <: usize
                })
              2sz
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
          (fun i ->
              Core.Num.from_str_radix_under_impl_6 (s.[ {
                      Core.Ops.Range.Range.f_start = i;
                      Core.Ops.Range.Range.f_end = i +. 2sz <: usize
                    } ]
                  <:
                  string)
                16ul
              <:
              Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError)
        <:
        Core.Iter.Adapters.Map.t_Map
          (Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
          (usize -> Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError))
  in
  Core.Result.expect_under_impl b "Error parsing hex string"

let from_literal_under_impl_16 (x: u128) : t_QueryCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_16 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type QueryCanvas"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Core.Convert.Into.into big_x

let from_signed_literal_under_impl_16 (x: i128) : t_QueryCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_16 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type QueryCanvas"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Core.Convert.Into.into big_x

let pow2_under_impl_16 (x: usize) : t_QueryCanvas =
  Core.Convert.Into.into ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. x
      <:
      Core.Ops.Bit.Shl.t_Output)

let bit_under_impl_16 (self: t_QueryCanvas) (i: usize) : bool =
  let _:Prims.unit =
    if
      ~.(i <.
        ((Core.Slice.len_under_impl (Rust_primitives.unsize self
                    .Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b
                <:
                slice u8)
            <:
            usize) *.
          8sz
          <:
          usize)
        <:
        bool)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l =
                          [
                            "the bit queried should be lower than the size of the integer representation: ";
                            " < "
                          ]
                        in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [
                            Core.Fmt.Rt.new_display_under_impl_1 i <: Core.Fmt.Rt.t_Argument;
                            Core.Fmt.Rt.new_display_under_impl_1 ((Core.Slice.len_under_impl (Rust_primitives.unsize
                                        self.Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b
                                      <:
                                      slice u8)
                                  <:
                                  usize) *.
                                8sz
                                <:
                                usize)
                            <:
                            Core.Fmt.Rt.t_Argument
                          ]
                        in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let (bigint: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into self
  in
  let (tmp: Num_bigint.Bigint.t_BigInt):Core.Ops.Bit.Shr.t_Output = bigint <<. i in
  ((Num_bigint.Bigint.to_bytes_le_under_impl_24 (tmp &.
          (Num_traits.Identities.One.one <: Num_bigint.Bigint.t_BigInt)
          <:
          Num_bigint.Bigint.t_BigInt)
      <:
      (Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      ._2.[ 0sz ]
    <:
    u8) =.
  1uy

let impl: Core.Convert.t_From t_QueryCanvas Num_bigint.Biguint.t_BigUint =
  {
    from
    =
    fun (x: Num_bigint.Biguint.t_BigUint) ->
      Core.Convert.From.from (Core.Convert.From.from x <: Num_bigint.Bigint.t_BigInt)
  }

let impl: Core.Convert.t_From t_QueryCanvas Num_bigint.Bigint.t_BigInt =
  {
    from
    =
    fun (x: Num_bigint.Bigint.t_BigInt) ->
      let max_value:Num_bigint.Bigint.t_BigInt = max_under_impl_16 in
      let _:Prims.unit =
        if ~.(x <=. max_value <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              [""; " is too large for type QueryCanvas!"]
                            in
                            assert_norm (List.Tot.length l == 2);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (let l =
                              [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let sign, repr:(Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
        Num_bigint.Bigint.to_bytes_be_under_impl_24 x
      in
      let _:Prims.unit =
        if Prims.op_AmpAmp (sign =. Num_bigint.Bigint.Sign_Minus) ~.false
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Std.Panicking.begin_panic "Trying to convert a negative number into an unsigned integer!"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let _:Prims.unit =
        if (Alloc.Vec.len_under_impl_1 repr <: usize) >. ((384sz +. 7sz <: usize) /. 8sz <: usize)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = [""; " is too large for type QueryCanvas"] in
                            assert_norm (List.Tot.length l == 2);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (let l =
                              [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let out:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
      let upper:usize = Core.Slice.len_under_impl (Rust_primitives.unsize out <: slice u8) in
      let lower:usize = upper -. (Alloc.Vec.len_under_impl_1 repr <: usize) in
      let _:Prims.unit =
        Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
          "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (out),\n            core::ops::range::Range {\n                f_start: lower,\n                f_end: upper,\n            },\n        ))),\n        &(deref(core::ops::deref::Deref::deref(&(deref(&(repr)))))),\n    )"

      in
      {
        Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b = out;
        Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_sign = sign;
        Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_signed = false
      }
  }

let impl: Core.Default.t_Default t_QueryCanvas =
  {
    default
    =
    fun  ->
      {
        Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b = Rust_primitives.Hax.repeat 0uy 48sz;
        Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
        Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_signed = false
      }
  }

let impl: Core.Convert.t_Into t_QueryCanvas Num_bigint.Bigint.t_BigInt =
  {
    into
    =
    fun (self: t_QueryCanvas) ->
      Num_bigint.Bigint.from_bytes_be_under_impl_24 self
          .Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_sign
        (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b <: slice u8)
  }

let impl: Core.Convert.t_Into t_QueryCanvas Num_bigint.Biguint.t_BigUint =
  {
    into
    =
    fun (self: t_QueryCanvas) ->
      Num_bigint.Biguint.from_bytes_be_under_impl_18 (Rust_primitives.unsize self
              .Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b
          <:
          slice u8)
  }

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

let from_hex_under_impl_15 (s: string) : t_QueryCanvas =
  Core.Convert.Into.into (Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
        (Core.Ops.Deref.Deref.deref (hex_string_to_bytes_under_impl_16 s
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      Num_bigint.Bigint.t_BigInt)

let from_be_bytes_under_impl_15 (v: slice u8) : t_QueryCanvas =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.len_under_impl v <: usize) <=. ((384sz +. 7sz <: usize) /. 8sz <: usize)
            <:
            bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Std.Panicking.begin_panic "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ()
  in
  let repr:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
  let upper:usize = Core.Slice.len_under_impl (Rust_primitives.unsize repr <: slice u8) in
  let lower:usize = upper -. (Core.Slice.len_under_impl v <: usize) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
      "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (repr),\n            core::ops::range::Range {\n                f_start: lower,\n                f_end: upper,\n            },\n        ))),\n        &(deref(deref(&(v)))),\n    )"

  in
  {
    Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b = repr;
    Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
    Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_signed = false
  }

let from_le_bytes_under_impl_15 (v: slice u8) : t_QueryCanvas =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.len_under_impl v <: usize) <=. ((384sz +. 7sz <: usize) /. 8sz <: usize)
            <:
            bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Std.Panicking.begin_panic "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ()
  in
  let repr:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
  let upper:usize = Core.Slice.len_under_impl (Rust_primitives.unsize repr <: slice u8) in
  let lower:usize = upper -. (Core.Slice.len_under_impl v <: usize) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
      "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (repr),\n            core::ops::range::Range {\n                f_start: lower,\n                f_end: upper,\n            },\n        ))),\n        &(deref(deref(&(v)))),\n    )"

  in
  Core.Convert.Into.into (Num_bigint.Bigint.from_bytes_le_under_impl_24 Num_bigint.Bigint.Sign_Plus
        (Rust_primitives.unsize repr <: slice u8)
      <:
      Num_bigint.Bigint.t_BigInt)

let to_be_bytes_under_impl_15 (self: t_QueryCanvas) : array u8 48sz =
  self.Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b

let to_le_bytes_under_impl_15 (self: t_QueryCanvas) : array u8 48sz =
  let x:Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
      (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_b <: slice u8)
  in
  let _, x_s:(Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Num_bigint.Bigint.to_bytes_le_under_impl_24 x
  in
  let repr:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
      "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (repr),\n            core::ops::range::Range {\n                f_start: 0,\n                f_end: alloc::vec::len_under_impl_1(&(x_s)),\n            },\n        ))),\n        &(deref(core::ops::deref::Deref::deref(&(deref(&(x_s)))))),\n    )"

  in
  repr

let comp_eq_under_impl_15 (self rhs: t_QueryCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a =. b
  then
    let one:t_QueryCanvas = from_literal_under_impl_16 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_ne_under_impl_15 (self rhs: t_QueryCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <>. b
  then
    let one:t_QueryCanvas = from_literal_under_impl_16 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gte_under_impl_15 (self rhs: t_QueryCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >=. b
  then
    let one:t_QueryCanvas = from_literal_under_impl_16 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gt_under_impl_15 (self rhs: t_QueryCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >. b
  then
    let one:t_QueryCanvas = from_literal_under_impl_16 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lte_under_impl_15 (self rhs: t_QueryCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <=. b
  then
    let one:t_QueryCanvas = from_literal_under_impl_16 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lt_under_impl_15 (self rhs: t_QueryCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <. b
  then
    let one:t_QueryCanvas = from_literal_under_impl_16 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let inv_under_impl_27 (self modval: t_QueryCanvas) : t_QueryCanvas =
  let (biguintmodval: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into modval
  in
  let m:Core.Ops.Arith.Sub.t_Output =
    biguintmodval -. (Core.Convert.From.from 2ul <: Num_bigint.Bigint.t_BigInt)
  in
  let (s: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  Core.Convert.Into.into (Num_bigint.Bigint.modpow_under_impl_24 s m biguintmodval
      <:
      Num_bigint.Bigint.t_BigInt)

let pow_felem_under_impl_27 (self exp modval: t_QueryCanvas) : t_QueryCanvas =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into exp in
  let (m: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into modval in
  let (c: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.modpow_under_impl_24 a b m
  in
  Core.Convert.Into.into c

let pow_under_impl_27 (self: t_QueryCanvas) (exp: u128) (modval: t_QueryCanvas) : t_QueryCanvas =
  pow_felem_under_impl_27 self
    (Core.Convert.Into.into (Core.Convert.From.from exp <: Num_bigint.Bigint.t_BigInt)
      <:
      t_QueryCanvas)
    modval

let rem_under_impl_27 (self n: t_QueryCanvas) : Core.Ops.Arith.Rem.t_Output = self %. n

let impl: Core.Ops.Arith.t_Add t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    add
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Add.t_Output = a +. b in
      let _:Prims.unit =
        if c >. (max_under_impl_16 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded addition overflow for type QueryCanvas"]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Sub t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    sub
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Sub.t_Output =
        if self.Hacspec_ovn.Schnorr.Random_oracle.QueryCanvas.f_signed
        then a -. b
        else
          Core.Option.unwrap_or_else_under_impl (Num_bigint.Bigint.checked_sub_under_impl_24 a b
              <:
              Core.Option.t_Option Num_bigint.Bigint.t_BigInt)
            (fun  ->
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                          (Rust_primitives.unsize (let l =
                                  ["bounded substraction underflow for type QueryCanvas"]
                                in
                                assert_norm (List.Tot.length l == 1);
                                Rust_primitives.Hax.array_of_list l)
                            <:
                            slice string)
                          (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                                <:
                                array Core.Fmt.Rt.t_Argument 0sz)
                            <:
                            slice Core.Fmt.Rt.t_Argument)
                        <:
                        Core.Fmt.t_Arguments)
                    <:
                    Rust_primitives.Hax.t_Never)
                <:
                Num_bigint.Bigint.t_BigInt)
      in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Mul t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    mul
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Mul.t_Output = a *. b in
      let _:Prims.unit =
        if c >. (max_under_impl_16 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded multiplication overflow for type QueryCanvas"]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Div t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    div
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type QueryCanvas"] in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let c:Core.Ops.Arith.Div.t_Output = a /. b in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Rem t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    rem
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type QueryCanvas"] in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let c:Core.Ops.Arith.Rem.t_Output = a %. b in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Bit.t_Not t_QueryCanvas =
  {
    output = t_QueryCanvas;
    not
    =
    fun (self: t_QueryCanvas) ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
          <:
          Rust_primitives.Hax.t_Never)
  }

let impl: Core.Ops.Bit.t_BitOr t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    bitor
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    bitxor
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_QueryCanvas t_QueryCanvas =
  {
    output = t_QueryCanvas;
    bitand
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_QueryCanvas usize =
  {
    output = t_QueryCanvas;
    shr
    =
    fun (self: t_QueryCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a <<. b <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_QueryCanvas usize =
  {
    output = t_QueryCanvas;
    shl
    =
    fun (self: t_QueryCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a >>. b <: Core.Ops.Bit.Shl.t_Output)
  }

let impl: Core.Cmp.t_PartialEq t_QueryCanvas t_QueryCanvas =
  {
    eq
    =
    fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      a =. b
  }

let impl: Core.Cmp.t_Eq t_QueryCanvas = {  }

let impl: Core.Cmp.t_PartialOrd t_QueryCanvas t_QueryCanvas =
  {
    partial_cmp
    =
    fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into other
      in
      Core.Cmp.PartialOrd.partial_cmp a b
  }

let impl: Core.Cmp.t_Ord t_QueryCanvas =
  {
    cmp
    =
    fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
      Core.Option.unwrap_under_impl (Core.Cmp.PartialOrd.partial_cmp self other
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering)
  }

let from_byte_seq_be_under_impl_8 (s: a) : t_QueryCanvas =
  from_be_bytes_under_impl_15 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
            (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                  <:
                  Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                (fun x -> Secret_integers.declassify_under_impl_2 x <: u8)
              <:
              Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                (Secret_integers.t_U8 -> u8))
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      slice u8)

let from_public_byte_seq_be_under_impl_8 (s: a) : t_QueryCanvas =
  from_be_bytes_under_impl_15 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
            (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                  <:
                  Core.Slice.Iter.t_Iter u8)
                (fun x -> x)
              <:
              Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      slice u8)

let to_byte_seq_be_under_impl_8 (self: t_QueryCanvas) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_15 self
                      <:
                      array u8 48sz)
                  <:
                  slice u8)
              <:
              Core.Slice.Iter.t_Iter u8)
            (fun x -> Secret_integers.classify_under_impl_2 x <: Secret_integers.t_U8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> Secret_integers.t_U8))
      <:
      Alloc.Vec.t_Vec Secret_integers.t_U8 Alloc.Alloc.t_Global)

let impl: Hacspec_lib.Traits.t_NumericCopy t_QueryCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_QueryCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_QueryCanvas = {  }

let impl: Hacspec_lib.Traits.t_Integer t_QueryCanvas =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_16 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_16 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_16 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_16 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_15 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
                      s
                    <:
                    string)
                  "0x"
                  ""
                <:
                Alloc.String.t_String)
            <:
            string));
    get_bit
    =
    (fun (self: t_QueryCanvas) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &.
        (Hacspec_lib.Traits.Integer.v_ONE <: t_QueryCanvas));
    set_bit
    =
    (fun (self: t_QueryCanvas) (b: t_QueryCanvas) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_QueryCanvas)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_QueryCanvas)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_QueryCanvas)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_QueryCanvas)
                      <:
                      bool))
              then
                let ():Prims.unit =
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO())"

                      <:
                      Rust_primitives.Hax.t_Never)
                in
                ()
            in
            ()
        in
        let tmp1:t_QueryCanvas =
          from_literal_under_impl_16 (~.(pub_u128 1sz >>. i <: u128) <: u128)
        in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_QueryCanvas) (pos: usize) (y: t_QueryCanvas) (yi: usize) ->
        let b:t_QueryCanvas = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_QueryCanvas) (n: usize) ->
        let _:Prims.unit =
          if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
          then
            let ():Prims.unit =
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                  <:
                  Rust_primitives.Hax.t_Never)
            in
            ()
        in
        ((Core.Clone.Clone.clone self <: t_QueryCanvas) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_QueryCanvas) (n: usize) ->
      let _:Prims.unit =
        if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ((Core.Clone.Clone.clone self <: t_QueryCanvas) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_QueryCanvas =
  {
    sub_mod
    =
    (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) (n: t_QueryCanvas) ->
        (self -. rhs <: Core.Ops.Arith.Sub.t_Output) %. n);
    add_mod
    =
    (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) (n: t_QueryCanvas) ->
        (self +. rhs <: Core.Ops.Arith.Add.t_Output) %. n);
    mul_mod
    =
    (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) (n: t_QueryCanvas) ->
        (self *. rhs <: Core.Ops.Arith.Mul.t_Output) %. n);
    pow_mod
    =
    (fun (self: t_QueryCanvas) (exp: t_QueryCanvas) (n: t_QueryCanvas) ->
        pow_felem_under_impl_27 self exp n);
    modulo = (fun (self: t_QueryCanvas) (n: t_QueryCanvas) -> self %. n);
    signed_modulo
    =
    (fun (self: t_QueryCanvas) (n: t_QueryCanvas) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_QueryCanvas) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_QueryCanvas =
  {
    max_val = (fun  -> max_value_under_impl_16);
    wrap_add = (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) -> self +. rhs);
    wrap_sub = (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) -> self -. rhs);
    wrap_mul = (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) -> self *. rhs);
    wrap_div = (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) -> self /. rhs);
    exp
    =
    (fun (self: t_QueryCanvas) (exp: u32) ->
        pow_under_impl_27 self
          (Core.Convert.Into.into exp <: u128)
          (Hacspec_lib.Traits.Numeric.max_val <: t_QueryCanvas));
    pow_self
    =
    (fun (self: t_QueryCanvas) (exp: t_QueryCanvas) ->
        pow_felem_under_impl_27 self
          (Core.Convert.Into.into exp <: t_QueryCanvas)
          (Hacspec_lib.Traits.Numeric.max_val <: t_QueryCanvas));
    divide = (fun (self: t_QueryCanvas) (rhs: t_QueryCanvas) -> self /. rhs);
    inv = (fun (self: t_QueryCanvas) (n: t_QueryCanvas) -> inv_under_impl_27 self n);
    equal = (fun (self: t_QueryCanvas) (other: t_QueryCanvas) -> self =. other);
    greater_than = (fun (self: t_QueryCanvas) (other: t_QueryCanvas) -> self >. other);
    greater_than_or_equal = (fun (self: t_QueryCanvas) (other: t_QueryCanvas) -> self >=. other);
    less_than = (fun (self: t_QueryCanvas) (other: t_QueryCanvas) -> self <. other);
    less_than_or_equal = (fun (self: t_QueryCanvas) (other: t_QueryCanvas) -> self >=. other);
    not_equal_bm
    =
    (fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
        if ~.(Hacspec_lib.Traits.Numeric.equal self other <: bool)
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_16 (pub_u128 0sz));
    equal_bm
    =
    (fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
        if Hacspec_lib.Traits.Numeric.equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_16 (pub_u128 0sz));
    greater_than_bm
    =
    (fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_16 (pub_u128 0sz));
    greater_than_or_equal_bm
    =
    (fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than_or_equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_16 (pub_u128 0sz));
    less_than_bm
    =
    (fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
        if Hacspec_lib.Traits.Numeric.less_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_16 (pub_u128 0sz));
    less_than_or_equal_bm
    =
    fun (self: t_QueryCanvas) (other: t_QueryCanvas) ->
      if Hacspec_lib.Traits.Numeric.less_than_or_equal self other
      then Hacspec_lib.Traits.Numeric.max_val
      else from_literal_under_impl_16 (pub_u128 0sz)
  }

type t_Query = | Query : t_QueryCanvas -> t_Query

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

let impl: Core.Convert.t_From t_Query t_QueryCanvas =
  {
    from
    =
    fun (x: t_QueryCanvas) ->
      Query
      (rem_under_impl_27 x
          (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QueryCanvas))
  }

let impl: Core.Convert.t_Into t_Query t_QueryCanvas =
  { into = fun (self: t_Query) -> self.Hacspec_ovn.Schnorr.Random_oracle.Query.0 }

let from_canvas_under_impl_64 (x: t_QueryCanvas) : t_Query =
  Query
  (rem_under_impl_27 x
      (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_QueryCanvas))

let into_canvas_under_impl_64 (self: t_Query) : t_QueryCanvas =
  self.Hacspec_ovn.Schnorr.Random_oracle.Query.0

let max_under_impl_64: t_QueryCanvas =
  from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

let declassify_under_impl_64 (self: t_Query) : Num_bigint.Bigint.t_BigInt =
  let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into a

let from_hex_under_impl_64 (s: string) : t_Query =
  Core.Convert.Into.into (from_hex_under_impl_15 s <: t_QueryCanvas)

let from_be_bytes_under_impl_64 (v: slice u8) : t_Query =
  Core.Convert.Into.into (from_be_bytes_under_impl_15 v <: t_QueryCanvas)

let to_be_bytes_under_impl_64 (self: t_Query) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_15 (Core.Convert.Into.into
                self
              <:
              t_QueryCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let from_le_bytes_under_impl_64 (v: slice u8) : t_Query =
  Core.Convert.Into.into (from_le_bytes_under_impl_15 v <: t_QueryCanvas)

let to_le_bytes_under_impl_64 (self: t_Query) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_le_bytes_under_impl_15 (Core.Convert.Into.into
                self
              <:
              t_QueryCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let bit_under_impl_64 (self: t_Query) (i: usize) : bool =
  bit_under_impl_16 (Core.Convert.Into.into self <: t_QueryCanvas) i

let from_literal_under_impl_64 (x: u128) : t_Query =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_64 <: t_QueryCanvas) <: Num_bigint.Biguint.t_BigUint)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type Query"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Query (Core.Convert.Into.into big_x)

let from_signed_literal_under_impl_64 (x: i128) : t_Query =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_64 <: t_QueryCanvas) <: Num_bigint.Biguint.t_BigUint)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type Query"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Query (Core.Convert.Into.into big_x)

let comp_eq_under_impl_64 (self rhs: t_Query) : t_Query =
  let (x: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_eq_under_impl_15 x (Core.Convert.Into.into rhs <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let comp_ne_under_impl_64 (self rhs: t_Query) : t_Query =
  let (x: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_ne_under_impl_15 x (Core.Convert.Into.into rhs <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let comp_gte_under_impl_64 (self rhs: t_Query) : t_Query =
  let (x: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gte_under_impl_15 x (Core.Convert.Into.into rhs <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let comp_gt_under_impl_64 (self rhs: t_Query) : t_Query =
  let (x: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gt_under_impl_15 x (Core.Convert.Into.into rhs <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let comp_lte_under_impl_64 (self rhs: t_Query) : t_Query =
  let (x: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lte_under_impl_15 x (Core.Convert.Into.into rhs <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let comp_lt_under_impl_64 (self rhs: t_Query) : t_Query =
  let (x: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lt_under_impl_15 x (Core.Convert.Into.into rhs <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let neg_under_impl_64 (self: t_Query) : t_Query =
  let (mod_val: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_QueryCanvas)
  in
  let (s: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  let (s: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into s in
  let (result: t_QueryCanvas):t_QueryCanvas =
    Core.Convert.Into.into (mod_val -. s <: Core.Ops.Arith.Sub.t_Output)
  in
  Core.Convert.Into.into result

let impl: Core.Cmp.t_PartialOrd t_Query t_Query =
  {
    partial_cmp
    =
    fun (self: t_Query) (other: t_Query) -> Core.Option.Option_Some (Core.Cmp.Ord.cmp self other)
  }

let impl: Core.Cmp.t_Ord t_Query =
  {
    cmp
    =
    fun (self: t_Query) (other: t_Query) ->
      Core.Cmp.Ord.cmp self.Hacspec_ovn.Schnorr.Random_oracle.Query.0
        other.Hacspec_ovn.Schnorr.Random_oracle.Query.0
  }

let impl: Core.Cmp.t_PartialEq t_Query t_Query =
  {
    eq
    =
    fun (self: t_Query) (other: t_Query) ->
      self.Hacspec_ovn.Schnorr.Random_oracle.Query.0 =.
      other.Hacspec_ovn.Schnorr.Random_oracle.Query.0
  }

let impl: Core.Cmp.t_Eq t_Query = {  }

let impl: Core.Ops.Arith.t_Add t_Query t_Query =
  {
    output = t_Query;
    add
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Add.t_Output = a +. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QueryCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Sub t_Query t_Query =
  {
    output = t_Query;
    sub
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QueryCanvas)
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Add.t_Output =
        if b >. a
        then
          ((Core.Clone.Clone.clone max <: Num_bigint.Biguint.t_BigUint) -. b
            <:
            Core.Ops.Arith.Sub.t_Output) +.
          a
        else a -. b
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Mul t_Query t_Query =
  {
    output = t_Query;
    mul
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Mul.t_Output = a *. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QueryCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Div t_Query t_Query =
  {
    output = t_Query;
    div = fun (self: t_Query) (rhs: t_Query) -> self *. (inv_under_impl_58 rhs <: t_Query)
  }

let impl: Core.Ops.Arith.t_Rem t_Query t_Query =
  {
    output = t_Query;
    rem
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = a %. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_15 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QueryCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Bit.t_Not t_Query =
  {
    output = t_Query;
    not
    =
    fun (self: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (~.a <: Core.Ops.Bit.Not.t_Output)
  }

let impl: Core.Ops.Bit.t_BitOr t_Query t_Query =
  {
    output = t_Query;
    bitor
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_Query t_Query =
  {
    output = t_Query;
    bitxor
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_Query t_Query =
  {
    output = t_Query;
    bitand
    =
    fun (self: t_Query) (rhs: t_Query) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      let (b: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_Query usize =
  {
    output = t_Query;
    shr
    =
    fun (self: t_Query) (rhs: usize) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a <<. rhs <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_Query usize =
  {
    output = t_Query;
    shl
    =
    fun (self: t_Query) (rhs: usize) ->
      let (a: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a >>. rhs <: Core.Ops.Bit.Shl.t_Output)
  }

let inv_under_impl_58 (self: t_Query) : t_Query =
  let (base: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (inv_under_impl_27 base (max_under_impl_64 <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let pow_felem_under_impl_58 (self exp: t_Query) : t_Query =
  let (base: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_felem_under_impl_27 base
        (Core.Convert.Into.into exp <: t_QueryCanvas)
        (max_under_impl_64 <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let pow_under_impl_58 (self: t_Query) (exp: u128) : t_Query =
  let (base: t_QueryCanvas):t_QueryCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_under_impl_27 base exp (max_under_impl_64 <: t_QueryCanvas)
      <:
      t_QueryCanvas)

let pow2_under_impl_58 (x: usize) : t_Query =
  Core.Convert.Into.into (pow2_under_impl_16 x <: t_QueryCanvas)

let from_byte_seq_be_under_impl_1 (s: a) : t_Query =
  Core.Convert.Into.into (from_be_bytes_under_impl_15 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (fun x -> Secret_integers.declassify_under_impl_2 x <: u8)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (Secret_integers.t_U8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_QueryCanvas)

let from_public_byte_seq_be_under_impl_1 (s: a) : t_Query =
  Core.Convert.Into.into (from_be_bytes_under_impl_15 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter u8)
                    (fun x -> x)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_QueryCanvas)

let to_byte_seq_be_under_impl_1 (self: t_Query) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_be_bytes_under_impl_64 self
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  slice u8)
              <:
              Core.Slice.Iter.t_Iter u8)
            (fun x -> Secret_integers.classify_under_impl_2 x <: Secret_integers.t_U8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> Secret_integers.t_U8))
      <:
      Alloc.Vec.t_Vec Secret_integers.t_U8 Alloc.Alloc.t_Global)

let to_public_byte_seq_be_under_impl_1 (self: t_Query) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_be_bytes_under_impl_64 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_byte_seq_le_under_impl_1 (s: a) : t_Query =
  Core.Convert.Into.into (from_le_bytes_under_impl_15 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (fun x -> Secret_integers.declassify_under_impl_2 x <: u8)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (Secret_integers.t_U8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_QueryCanvas)

let from_public_byte_seq_le_under_impl_1 (s: a) : t_Query =
  Core.Convert.Into.into (from_le_bytes_under_impl_15 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter u8)
                    (fun x -> x)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_QueryCanvas)

let to_byte_seq_le_under_impl_1 (self: t_Query) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_le_bytes_under_impl_64 self
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  slice u8)
              <:
              Core.Slice.Iter.t_Iter u8)
            (fun x -> Secret_integers.classify_under_impl_2 x <: Secret_integers.t_U8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> Secret_integers.t_U8))
      <:
      Alloc.Vec.t_Vec Secret_integers.t_U8 Alloc.Alloc.t_Global)

let to_public_byte_seq_le_under_impl_1 (self: t_Query) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_le_bytes_under_impl_64 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_secret_literal_under_impl_1 (x: Secret_integers.t_U128) : t_Query =
  Core.Convert.Into.into (from_literal_under_impl_16 (Secret_integers.declassify_under_impl_126 x
          <:
          u128)
      <:
      t_QueryCanvas)

let impl: Hacspec_lib.Traits.t_NumericCopy t_Query = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_Query = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_Query = {  }

let impl: Hacspec_lib.Traits.t_Integer t_Query =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_64 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_64 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_64 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_64 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_64 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
                      s
                    <:
                    string)
                  "0x"
                  ""
                <:
                Alloc.String.t_String)
            <:
            string));
    get_bit
    =
    (fun (self: t_Query) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &. (Hacspec_lib.Traits.Integer.v_ONE <: t_Query));
    set_bit
    =
    (fun (self: t_Query) (b: t_Query) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_Query)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_Query)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_Query)
                      <:
                      bool))
              then
                let ():Prims.unit =
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO())"

                      <:
                      Rust_primitives.Hax.t_Never)
                in
                ()
            in
            ()
        in
        let tmp1:t_Query = from_literal_under_impl_64 (~.(pub_u128 1sz >>. i <: u128) <: u128) in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_Query) (pos: usize) (y: t_Query) (yi: usize) ->
        let b:t_Query = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_Query) (n: usize) ->
        let _:Prims.unit =
          if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
          then
            let ():Prims.unit =
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                  <:
                  Rust_primitives.Hax.t_Never)
            in
            ()
        in
        ((Core.Clone.Clone.clone self <: t_Query) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_Query) (n: usize) ->
      let _:Prims.unit =
        if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ((Core.Clone.Clone.clone self <: t_Query) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_Query =
  {
    sub_mod = (fun (self: t_Query) (rhs: t_Query) (n: t_Query) -> self -. rhs);
    add_mod = (fun (self: t_Query) (rhs: t_Query) (n: t_Query) -> self +. rhs);
    mul_mod = (fun (self: t_Query) (rhs: t_Query) (n: t_Query) -> self *. rhs);
    pow_mod = (fun (self: t_Query) (exp: t_Query) (n: t_Query) -> pow_felem_under_impl_58 self exp);
    modulo = (fun (self: t_Query) (n: t_Query) -> self %. n);
    signed_modulo
    =
    (fun (self: t_Query) (n: t_Query) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_Query) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_Query =
  {
    max_val
    =
    (fun  ->
        Core.Convert.Into.into ((max_under_impl_64 <: t_QueryCanvas) -.
            (from_literal_under_impl_16 (pub_u128 1sz) <: t_QueryCanvas)
            <:
            Core.Ops.Arith.Sub.t_Output));
    wrap_add = (fun (self: t_Query) (rhs: t_Query) -> self +. rhs);
    wrap_sub = (fun (self: t_Query) (rhs: t_Query) -> self -. rhs);
    wrap_mul = (fun (self: t_Query) (rhs: t_Query) -> self *. rhs);
    wrap_div = (fun (self: t_Query) (rhs: t_Query) -> self /. rhs);
    exp
    =
    (fun (self: t_Query) (exp: u32) -> pow_under_impl_58 self (Core.Convert.Into.into exp <: u128));
    pow_self = (fun (self: t_Query) (exp: t_Query) -> pow_felem_under_impl_58 self exp);
    divide = (fun (self: t_Query) (rhs: t_Query) -> self /. rhs);
    inv = (fun (self: t_Query) (n: t_Query) -> inv_under_impl_58 self);
    equal = (fun (self: t_Query) (other: t_Query) -> self =. other);
    greater_than = (fun (self: t_Query) (other: t_Query) -> self >. other);
    greater_than_or_equal = (fun (self: t_Query) (other: t_Query) -> self >=. other);
    less_than = (fun (self: t_Query) (other: t_Query) -> self <. other);
    less_than_or_equal = (fun (self: t_Query) (other: t_Query) -> self <=. other);
    not_equal_bm
    =
    (fun (self: t_Query) (other: t_Query) ->
        if self <>. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Query) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    equal_bm
    =
    (fun (self: t_Query) (other: t_Query) ->
        if self =. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Query) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_bm
    =
    (fun (self: t_Query) (other: t_Query) ->
        if self >. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Query) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_or_equal_bm
    =
    (fun (self: t_Query) (other: t_Query) ->
        if self >=. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Query) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_bm
    =
    (fun (self: t_Query) (other: t_Query) ->
        if self <. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Query) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_or_equal_bm
    =
    fun (self: t_Query) (other: t_Query) ->
      if self <=. other
      then
        ((Hacspec_lib.Traits.Integer.v_ONE <: t_Query) >>. (384sz -. 1sz <: usize)
          <:
          Core.Ops.Bit.Shl.t_Output) -.
        (Hacspec_lib.Traits.Integer.v_ONE <: t_Query)
      else Hacspec_lib.Traits.Integer.v_ZERO
  }

type t_RandomCanvas = {
  f_b:array u8 48sz;
  f_sign:Num_bigint.Bigint.t_Sign;
  f_signed:bool
}

let max_under_impl_83: Core.Ops.Arith.Sub.t_Output =
  ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. 384l <: Core.Ops.Bit.Shl.t_Output) -.
  (Num_traits.Identities.One.one <: Num_bigint.Bigint.t_BigInt)

let max_value_under_impl_83: t_RandomCanvas =
  Core.Convert.From.from (max_under_impl_83 <: Num_bigint.Bigint.t_BigInt)

let hex_string_to_bytes_under_impl_83 (s: string) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let s:Alloc.String.t_String =
    if ((Core.Str.len_under_impl s <: usize) %. 2sz <: usize) <>. 0sz
    then
      let x:Alloc.String.t_String = Alloc.String.ToString.to_string "0" in
      let x:Alloc.String.t_String = Alloc.String.push_str_under_impl x s in
      x
    else Alloc.String.ToString.to_string s
  in
  let _:Prims.unit =
    if ~.(((Alloc.String.len_under_impl s <: usize) %. 2sz <: usize) =. 0sz <: bool)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["length of hex string "; ": "] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [
                            Core.Fmt.Rt.new_display_under_impl_1 s <: Core.Fmt.Rt.t_Argument;
                            Core.Fmt.Rt.new_display_under_impl_1 (Alloc.String.len_under_impl s
                                <:
                                usize)
                            <:
                            Core.Fmt.Rt.t_Argument
                          ]
                        in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let
  (b: Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Core.Num.Error.t_ParseIntError):Core.Result.t_Result
    (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Core.Num.Error.t_ParseIntError =
    Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end = Alloc.String.len_under_impl s <: usize
                })
              2sz
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
          (fun i ->
              Core.Num.from_str_radix_under_impl_6 (s.[ {
                      Core.Ops.Range.Range.f_start = i;
                      Core.Ops.Range.Range.f_end = i +. 2sz <: usize
                    } ]
                  <:
                  string)
                16ul
              <:
              Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError)
        <:
        Core.Iter.Adapters.Map.t_Map
          (Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
          (usize -> Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError))
  in
  Core.Result.expect_under_impl b "Error parsing hex string"

let from_literal_under_impl_83 (x: u128) : t_RandomCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_83 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type RandomCanvas"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Core.Convert.Into.into big_x

let from_signed_literal_under_impl_83 (x: i128) : t_RandomCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_83 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type RandomCanvas"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Core.Convert.Into.into big_x

let pow2_under_impl_83 (x: usize) : t_RandomCanvas =
  Core.Convert.Into.into ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. x
      <:
      Core.Ops.Bit.Shl.t_Output)

let bit_under_impl_83 (self: t_RandomCanvas) (i: usize) : bool =
  let _:Prims.unit =
    if
      ~.(i <.
        ((Core.Slice.len_under_impl (Rust_primitives.unsize self
                    .Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b
                <:
                slice u8)
            <:
            usize) *.
          8sz
          <:
          usize)
        <:
        bool)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l =
                          [
                            "the bit queried should be lower than the size of the integer representation: ";
                            " < "
                          ]
                        in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [
                            Core.Fmt.Rt.new_display_under_impl_1 i <: Core.Fmt.Rt.t_Argument;
                            Core.Fmt.Rt.new_display_under_impl_1 ((Core.Slice.len_under_impl (Rust_primitives.unsize
                                        self.Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b
                                      <:
                                      slice u8)
                                  <:
                                  usize) *.
                                8sz
                                <:
                                usize)
                            <:
                            Core.Fmt.Rt.t_Argument
                          ]
                        in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let (bigint: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into self
  in
  let (tmp: Num_bigint.Bigint.t_BigInt):Core.Ops.Bit.Shr.t_Output = bigint <<. i in
  ((Num_bigint.Bigint.to_bytes_le_under_impl_24 (tmp &.
          (Num_traits.Identities.One.one <: Num_bigint.Bigint.t_BigInt)
          <:
          Num_bigint.Bigint.t_BigInt)
      <:
      (Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      ._2.[ 0sz ]
    <:
    u8) =.
  1uy

let impl: Core.Convert.t_From t_RandomCanvas Num_bigint.Biguint.t_BigUint =
  {
    from
    =
    fun (x: Num_bigint.Biguint.t_BigUint) ->
      Core.Convert.From.from (Core.Convert.From.from x <: Num_bigint.Bigint.t_BigInt)
  }

let impl: Core.Convert.t_From t_RandomCanvas Num_bigint.Bigint.t_BigInt =
  {
    from
    =
    fun (x: Num_bigint.Bigint.t_BigInt) ->
      let max_value:Num_bigint.Bigint.t_BigInt = max_under_impl_83 in
      let _:Prims.unit =
        if ~.(x <=. max_value <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              [""; " is too large for type RandomCanvas!"]
                            in
                            assert_norm (List.Tot.length l == 2);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (let l =
                              [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let sign, repr:(Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
        Num_bigint.Bigint.to_bytes_be_under_impl_24 x
      in
      let _:Prims.unit =
        if Prims.op_AmpAmp (sign =. Num_bigint.Bigint.Sign_Minus) ~.false
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Std.Panicking.begin_panic "Trying to convert a negative number into an unsigned integer!"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let _:Prims.unit =
        if (Alloc.Vec.len_under_impl_1 repr <: usize) >. ((384sz +. 7sz <: usize) /. 8sz <: usize)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              [""; " is too large for type RandomCanvas"]
                            in
                            assert_norm (List.Tot.length l == 2);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (let l =
                              [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let out:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
      let upper:usize = Core.Slice.len_under_impl (Rust_primitives.unsize out <: slice u8) in
      let lower:usize = upper -. (Alloc.Vec.len_under_impl_1 repr <: usize) in
      let _:Prims.unit =
        Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
          "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (out),\n            core::ops::range::Range {\n                f_start: lower,\n                f_end: upper,\n            },\n        ))),\n        &(deref(core::ops::deref::Deref::deref(&(deref(&(repr)))))),\n    )"

      in
      {
        Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b = out;
        Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_sign = sign;
        Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_signed = false
      }
  }

let impl: Core.Default.t_Default t_RandomCanvas =
  {
    default
    =
    fun  ->
      {
        Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b = Rust_primitives.Hax.repeat 0uy 48sz;
        Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
        Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_signed = false
      }
  }

let impl: Core.Convert.t_Into t_RandomCanvas Num_bigint.Bigint.t_BigInt =
  {
    into
    =
    fun (self: t_RandomCanvas) ->
      Num_bigint.Bigint.from_bytes_be_under_impl_24 self
          .Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_sign
        (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b <: slice u8)
  }

let impl: Core.Convert.t_Into t_RandomCanvas Num_bigint.Biguint.t_BigUint =
  {
    into
    =
    fun (self: t_RandomCanvas) ->
      Num_bigint.Biguint.from_bytes_be_under_impl_18 (Rust_primitives.unsize self
              .Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b
          <:
          slice u8)
  }

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

let from_hex_under_impl_82 (s: string) : t_RandomCanvas =
  Core.Convert.Into.into (Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
        (Core.Ops.Deref.Deref.deref (hex_string_to_bytes_under_impl_83 s
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      Num_bigint.Bigint.t_BigInt)

let from_be_bytes_under_impl_82 (v: slice u8) : t_RandomCanvas =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.len_under_impl v <: usize) <=. ((384sz +. 7sz <: usize) /. 8sz <: usize)
            <:
            bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Std.Panicking.begin_panic "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ()
  in
  let repr:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
  let upper:usize = Core.Slice.len_under_impl (Rust_primitives.unsize repr <: slice u8) in
  let lower:usize = upper -. (Core.Slice.len_under_impl v <: usize) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
      "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (repr),\n            core::ops::range::Range {\n                f_start: lower,\n                f_end: upper,\n            },\n        ))),\n        &(deref(deref(&(v)))),\n    )"

  in
  {
    Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b = repr;
    Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
    Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_signed = false
  }

let from_le_bytes_under_impl_82 (v: slice u8) : t_RandomCanvas =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.len_under_impl v <: usize) <=. ((384sz +. 7sz <: usize) /. 8sz <: usize)
            <:
            bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Std.Panicking.begin_panic "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ()
  in
  let repr:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
  let upper:usize = Core.Slice.len_under_impl (Rust_primitives.unsize repr <: slice u8) in
  let lower:usize = upper -. (Core.Slice.len_under_impl v <: usize) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
      "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (repr),\n            core::ops::range::Range {\n                f_start: lower,\n                f_end: upper,\n            },\n        ))),\n        &(deref(deref(&(v)))),\n    )"

  in
  Core.Convert.Into.into (Num_bigint.Bigint.from_bytes_le_under_impl_24 Num_bigint.Bigint.Sign_Plus
        (Rust_primitives.unsize repr <: slice u8)
      <:
      Num_bigint.Bigint.t_BigInt)

let to_be_bytes_under_impl_82 (self: t_RandomCanvas) : array u8 48sz =
  self.Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b

let to_le_bytes_under_impl_82 (self: t_RandomCanvas) : array u8 48sz =
  let x:Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
      (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_b <: slice u8)
  in
  let _, x_s:(Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Num_bigint.Bigint.to_bytes_le_under_impl_24 x
  in
  let repr:array u8 48sz = Rust_primitives.Hax.repeat 0uy 48sz in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "RefMut:The mutation of this &mut is not allowed here.\n"
      "core::slice::copy_from_slice_under_impl(\n        &mut (deref(core::ops::index::IndexMut::index_mut(\n            &mut (repr),\n            core::ops::range::Range {\n                f_start: 0,\n                f_end: alloc::vec::len_under_impl_1(&(x_s)),\n            },\n        ))),\n        &(deref(core::ops::deref::Deref::deref(&(deref(&(x_s)))))),\n    )"

  in
  repr

let comp_eq_under_impl_82 (self rhs: t_RandomCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a =. b
  then
    let one:t_RandomCanvas = from_literal_under_impl_83 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_ne_under_impl_82 (self rhs: t_RandomCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <>. b
  then
    let one:t_RandomCanvas = from_literal_under_impl_83 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gte_under_impl_82 (self rhs: t_RandomCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >=. b
  then
    let one:t_RandomCanvas = from_literal_under_impl_83 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gt_under_impl_82 (self rhs: t_RandomCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >. b
  then
    let one:t_RandomCanvas = from_literal_under_impl_83 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lte_under_impl_82 (self rhs: t_RandomCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <=. b
  then
    let one:t_RandomCanvas = from_literal_under_impl_83 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lt_under_impl_82 (self rhs: t_RandomCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <. b
  then
    let one:t_RandomCanvas = from_literal_under_impl_83 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let inv_under_impl_94 (self modval: t_RandomCanvas) : t_RandomCanvas =
  let (biguintmodval: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into modval
  in
  let m:Core.Ops.Arith.Sub.t_Output =
    biguintmodval -. (Core.Convert.From.from 2ul <: Num_bigint.Bigint.t_BigInt)
  in
  let (s: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  Core.Convert.Into.into (Num_bigint.Bigint.modpow_under_impl_24 s m biguintmodval
      <:
      Num_bigint.Bigint.t_BigInt)

let pow_felem_under_impl_94 (self exp modval: t_RandomCanvas) : t_RandomCanvas =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into exp in
  let (m: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into modval in
  let (c: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.modpow_under_impl_24 a b m
  in
  Core.Convert.Into.into c

let pow_under_impl_94 (self: t_RandomCanvas) (exp: u128) (modval: t_RandomCanvas) : t_RandomCanvas =
  pow_felem_under_impl_94 self
    (Core.Convert.Into.into (Core.Convert.From.from exp <: Num_bigint.Bigint.t_BigInt)
      <:
      t_RandomCanvas)
    modval

let rem_under_impl_94 (self n: t_RandomCanvas) : Core.Ops.Arith.Rem.t_Output = self %. n

let impl: Core.Ops.Arith.t_Add t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    add
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Add.t_Output = a +. b in
      let _:Prims.unit =
        if c >. (max_under_impl_83 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded addition overflow for type RandomCanvas"]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Sub t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    sub
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Sub.t_Output =
        if self.Hacspec_ovn.Schnorr.Random_oracle.RandomCanvas.f_signed
        then a -. b
        else
          Core.Option.unwrap_or_else_under_impl (Num_bigint.Bigint.checked_sub_under_impl_24 a b
              <:
              Core.Option.t_Option Num_bigint.Bigint.t_BigInt)
            (fun  ->
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                          (Rust_primitives.unsize (let l =
                                  ["bounded substraction underflow for type RandomCanvas"]
                                in
                                assert_norm (List.Tot.length l == 1);
                                Rust_primitives.Hax.array_of_list l)
                            <:
                            slice string)
                          (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                                <:
                                array Core.Fmt.Rt.t_Argument 0sz)
                            <:
                            slice Core.Fmt.Rt.t_Argument)
                        <:
                        Core.Fmt.t_Arguments)
                    <:
                    Rust_primitives.Hax.t_Never)
                <:
                Num_bigint.Bigint.t_BigInt)
      in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Mul t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    mul
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Mul.t_Output = a *. b in
      let _:Prims.unit =
        if c >. (max_under_impl_83 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded multiplication overflow for type RandomCanvas"]
                            in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Div t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    div
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type RandomCanvas"] in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let c:Core.Ops.Arith.Div.t_Output = a /. b in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Arith.t_Rem t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    rem
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type RandomCanvas"] in
                            assert_norm (List.Tot.length l == 1);
                            Rust_primitives.Hax.array_of_list l)
                        <:
                        slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.none_under_impl_1
                            <:
                            array Core.Fmt.Rt.t_Argument 0sz)
                        <:
                        slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let c:Core.Ops.Arith.Rem.t_Output = a %. b in
      Core.Convert.Into.into c
  }

let impl: Core.Ops.Bit.t_Not t_RandomCanvas =
  {
    output = t_RandomCanvas;
    not
    =
    fun (self: t_RandomCanvas) ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
          <:
          Rust_primitives.Hax.t_Never)
  }

let impl: Core.Ops.Bit.t_BitOr t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    bitor
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    bitxor
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_RandomCanvas t_RandomCanvas =
  {
    output = t_RandomCanvas;
    bitand
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_RandomCanvas usize =
  {
    output = t_RandomCanvas;
    shr
    =
    fun (self: t_RandomCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a <<. b <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_RandomCanvas usize =
  {
    output = t_RandomCanvas;
    shl
    =
    fun (self: t_RandomCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a >>. b <: Core.Ops.Bit.Shl.t_Output)
  }

let impl: Core.Cmp.t_PartialEq t_RandomCanvas t_RandomCanvas =
  {
    eq
    =
    fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      a =. b
  }

let impl: Core.Cmp.t_Eq t_RandomCanvas = {  }

let impl: Core.Cmp.t_PartialOrd t_RandomCanvas t_RandomCanvas =
  {
    partial_cmp
    =
    fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into other
      in
      Core.Cmp.PartialOrd.partial_cmp a b
  }

let impl: Core.Cmp.t_Ord t_RandomCanvas =
  {
    cmp
    =
    fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
      Core.Option.unwrap_under_impl (Core.Cmp.PartialOrd.partial_cmp self other
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering)
  }

let from_byte_seq_be_under_impl_75 (s: a) : t_RandomCanvas =
  from_be_bytes_under_impl_82 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
            (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                  <:
                  Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                (fun x -> Secret_integers.declassify_under_impl_2 x <: u8)
              <:
              Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                (Secret_integers.t_U8 -> u8))
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      slice u8)

let from_public_byte_seq_be_under_impl_75 (s: a) : t_RandomCanvas =
  from_be_bytes_under_impl_82 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
            (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                  <:
                  Core.Slice.Iter.t_Iter u8)
                (fun x -> x)
              <:
              Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      slice u8)

let to_byte_seq_be_under_impl_75 (self: t_RandomCanvas) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_82 self
                      <:
                      array u8 48sz)
                  <:
                  slice u8)
              <:
              Core.Slice.Iter.t_Iter u8)
            (fun x -> Secret_integers.classify_under_impl_2 x <: Secret_integers.t_U8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> Secret_integers.t_U8))
      <:
      Alloc.Vec.t_Vec Secret_integers.t_U8 Alloc.Alloc.t_Global)

let impl: Hacspec_lib.Traits.t_NumericCopy t_RandomCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_RandomCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_RandomCanvas = {  }

let impl: Hacspec_lib.Traits.t_Integer t_RandomCanvas =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_83 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_83 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_83 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_83 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_82 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
                      s
                    <:
                    string)
                  "0x"
                  ""
                <:
                Alloc.String.t_String)
            <:
            string));
    get_bit
    =
    (fun (self: t_RandomCanvas) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &.
        (Hacspec_lib.Traits.Integer.v_ONE <: t_RandomCanvas));
    set_bit
    =
    (fun (self: t_RandomCanvas) (b: t_RandomCanvas) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_RandomCanvas)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_RandomCanvas)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_RandomCanvas)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_RandomCanvas)
                      <:
                      bool))
              then
                let ():Prims.unit =
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO())"

                      <:
                      Rust_primitives.Hax.t_Never)
                in
                ()
            in
            ()
        in
        let tmp1:t_RandomCanvas =
          from_literal_under_impl_83 (~.(pub_u128 1sz >>. i <: u128) <: u128)
        in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_RandomCanvas) (pos: usize) (y: t_RandomCanvas) (yi: usize) ->
        let b:t_RandomCanvas = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_RandomCanvas) (n: usize) ->
        let _:Prims.unit =
          if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
          then
            let ():Prims.unit =
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                  <:
                  Rust_primitives.Hax.t_Never)
            in
            ()
        in
        ((Core.Clone.Clone.clone self <: t_RandomCanvas) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_RandomCanvas) (n: usize) ->
      let _:Prims.unit =
        if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ((Core.Clone.Clone.clone self <: t_RandomCanvas) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_RandomCanvas =
  {
    sub_mod
    =
    (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) (n: t_RandomCanvas) ->
        (self -. rhs <: Core.Ops.Arith.Sub.t_Output) %. n);
    add_mod
    =
    (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) (n: t_RandomCanvas) ->
        (self +. rhs <: Core.Ops.Arith.Add.t_Output) %. n);
    mul_mod
    =
    (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) (n: t_RandomCanvas) ->
        (self *. rhs <: Core.Ops.Arith.Mul.t_Output) %. n);
    pow_mod
    =
    (fun (self: t_RandomCanvas) (exp: t_RandomCanvas) (n: t_RandomCanvas) ->
        pow_felem_under_impl_94 self exp n);
    modulo = (fun (self: t_RandomCanvas) (n: t_RandomCanvas) -> self %. n);
    signed_modulo
    =
    (fun (self: t_RandomCanvas) (n: t_RandomCanvas) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_RandomCanvas) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_RandomCanvas =
  {
    max_val = (fun  -> max_value_under_impl_83);
    wrap_add = (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) -> self +. rhs);
    wrap_sub = (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) -> self -. rhs);
    wrap_mul = (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) -> self *. rhs);
    wrap_div = (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) -> self /. rhs);
    exp
    =
    (fun (self: t_RandomCanvas) (exp: u32) ->
        pow_under_impl_94 self
          (Core.Convert.Into.into exp <: u128)
          (Hacspec_lib.Traits.Numeric.max_val <: t_RandomCanvas));
    pow_self
    =
    (fun (self: t_RandomCanvas) (exp: t_RandomCanvas) ->
        pow_felem_under_impl_94 self
          (Core.Convert.Into.into exp <: t_RandomCanvas)
          (Hacspec_lib.Traits.Numeric.max_val <: t_RandomCanvas));
    divide = (fun (self: t_RandomCanvas) (rhs: t_RandomCanvas) -> self /. rhs);
    inv = (fun (self: t_RandomCanvas) (n: t_RandomCanvas) -> inv_under_impl_94 self n);
    equal = (fun (self: t_RandomCanvas) (other: t_RandomCanvas) -> self =. other);
    greater_than = (fun (self: t_RandomCanvas) (other: t_RandomCanvas) -> self >. other);
    greater_than_or_equal = (fun (self: t_RandomCanvas) (other: t_RandomCanvas) -> self >=. other);
    less_than = (fun (self: t_RandomCanvas) (other: t_RandomCanvas) -> self <. other);
    less_than_or_equal = (fun (self: t_RandomCanvas) (other: t_RandomCanvas) -> self >=. other);
    not_equal_bm
    =
    (fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
        if ~.(Hacspec_lib.Traits.Numeric.equal self other <: bool)
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_83 (pub_u128 0sz));
    equal_bm
    =
    (fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
        if Hacspec_lib.Traits.Numeric.equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_83 (pub_u128 0sz));
    greater_than_bm
    =
    (fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_83 (pub_u128 0sz));
    greater_than_or_equal_bm
    =
    (fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than_or_equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_83 (pub_u128 0sz));
    less_than_bm
    =
    (fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
        if Hacspec_lib.Traits.Numeric.less_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_83 (pub_u128 0sz));
    less_than_or_equal_bm
    =
    fun (self: t_RandomCanvas) (other: t_RandomCanvas) ->
      if Hacspec_lib.Traits.Numeric.less_than_or_equal self other
      then Hacspec_lib.Traits.Numeric.max_val
      else from_literal_under_impl_83 (pub_u128 0sz)
  }

type t_Random = | Random : t_RandomCanvas -> t_Random

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

let impl: Core.Convert.t_From t_Random t_RandomCanvas =
  {
    from
    =
    fun (x: t_RandomCanvas) ->
      Random
      (rem_under_impl_94 x
          (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_RandomCanvas))
  }

let impl: Core.Convert.t_Into t_Random t_RandomCanvas =
  { into = fun (self: t_Random) -> self.Hacspec_ovn.Schnorr.Random_oracle.Random.0 }

let from_canvas_under_impl_131 (x: t_RandomCanvas) : t_Random =
  Random
  (rem_under_impl_94 x
      (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_RandomCanvas))

let into_canvas_under_impl_131 (self: t_Random) : t_RandomCanvas =
  self.Hacspec_ovn.Schnorr.Random_oracle.Random.0

let max_under_impl_131: t_RandomCanvas =
  from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

let declassify_under_impl_131 (self: t_Random) : Num_bigint.Bigint.t_BigInt =
  let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into a

let from_hex_under_impl_131 (s: string) : t_Random =
  Core.Convert.Into.into (from_hex_under_impl_82 s <: t_RandomCanvas)

let from_be_bytes_under_impl_131 (v: slice u8) : t_Random =
  Core.Convert.Into.into (from_be_bytes_under_impl_82 v <: t_RandomCanvas)

let to_be_bytes_under_impl_131 (self: t_Random) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_82 (Core.Convert.Into.into
                self
              <:
              t_RandomCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let from_le_bytes_under_impl_131 (v: slice u8) : t_Random =
  Core.Convert.Into.into (from_le_bytes_under_impl_82 v <: t_RandomCanvas)

let to_le_bytes_under_impl_131 (self: t_Random) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_le_bytes_under_impl_82 (Core.Convert.Into.into
                self
              <:
              t_RandomCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let bit_under_impl_131 (self: t_Random) (i: usize) : bool =
  bit_under_impl_83 (Core.Convert.Into.into self <: t_RandomCanvas) i

let from_literal_under_impl_131 (x: u128) : t_Random =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_131 <: t_RandomCanvas) <: Num_bigint.Biguint.t_BigUint
      )
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type Random"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Random (Core.Convert.Into.into big_x)

let from_signed_literal_under_impl_131 (x: i128) : t_Random =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_131 <: t_RandomCanvas) <: Num_bigint.Biguint.t_BigUint
      )
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type Random"] in
                        assert_norm (List.Tot.length l == 2);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice string)
                  (Rust_primitives.unsize (let l =
                          [Core.Fmt.Rt.new_display_under_impl_1 x <: Core.Fmt.Rt.t_Argument]
                        in
                        assert_norm (List.Tot.length l == 1);
                        Rust_primitives.Hax.array_of_list l)
                    <:
                    slice Core.Fmt.Rt.t_Argument)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Random (Core.Convert.Into.into big_x)

let comp_eq_under_impl_131 (self rhs: t_Random) : t_Random =
  let (x: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_eq_under_impl_82 x (Core.Convert.Into.into rhs <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let comp_ne_under_impl_131 (self rhs: t_Random) : t_Random =
  let (x: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_ne_under_impl_82 x (Core.Convert.Into.into rhs <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let comp_gte_under_impl_131 (self rhs: t_Random) : t_Random =
  let (x: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gte_under_impl_82 x (Core.Convert.Into.into rhs <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let comp_gt_under_impl_131 (self rhs: t_Random) : t_Random =
  let (x: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gt_under_impl_82 x (Core.Convert.Into.into rhs <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let comp_lte_under_impl_131 (self rhs: t_Random) : t_Random =
  let (x: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lte_under_impl_82 x (Core.Convert.Into.into rhs <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let comp_lt_under_impl_131 (self rhs: t_Random) : t_Random =
  let (x: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lt_under_impl_82 x (Core.Convert.Into.into rhs <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let neg_under_impl_131 (self: t_Random) : t_Random =
  let (mod_val: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_RandomCanvas)
  in
  let (s: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  let (s: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into s in
  let (result: t_RandomCanvas):t_RandomCanvas =
    Core.Convert.Into.into (mod_val -. s <: Core.Ops.Arith.Sub.t_Output)
  in
  Core.Convert.Into.into result

let impl: Core.Cmp.t_PartialOrd t_Random t_Random =
  {
    partial_cmp
    =
    fun (self: t_Random) (other: t_Random) -> Core.Option.Option_Some (Core.Cmp.Ord.cmp self other)
  }

let impl: Core.Cmp.t_Ord t_Random =
  {
    cmp
    =
    fun (self: t_Random) (other: t_Random) ->
      Core.Cmp.Ord.cmp self.Hacspec_ovn.Schnorr.Random_oracle.Random.0
        other.Hacspec_ovn.Schnorr.Random_oracle.Random.0
  }

let impl: Core.Cmp.t_PartialEq t_Random t_Random =
  {
    eq
    =
    fun (self: t_Random) (other: t_Random) ->
      self.Hacspec_ovn.Schnorr.Random_oracle.Random.0 =.
      other.Hacspec_ovn.Schnorr.Random_oracle.Random.0
  }

let impl: Core.Cmp.t_Eq t_Random = {  }

let impl: Core.Ops.Arith.t_Add t_Random t_Random =
  {
    output = t_Random;
    add
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Add.t_Output = a +. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_RandomCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Sub t_Random t_Random =
  {
    output = t_Random;
    sub
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_RandomCanvas)
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Add.t_Output =
        if b >. a
        then
          ((Core.Clone.Clone.clone max <: Num_bigint.Biguint.t_BigUint) -. b
            <:
            Core.Ops.Arith.Sub.t_Output) +.
          a
        else a -. b
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Mul t_Random t_Random =
  {
    output = t_Random;
    mul
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Mul.t_Output = a *. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_RandomCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Div t_Random t_Random =
  {
    output = t_Random;
    div = fun (self: t_Random) (rhs: t_Random) -> self *. (inv_under_impl_125 rhs <: t_Random)
  }

let impl: Core.Ops.Arith.t_Rem t_Random t_Random =
  {
    output = t_Random;
    rem
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = a %. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_82 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_RandomCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Bit.t_Not t_Random =
  {
    output = t_Random;
    not
    =
    fun (self: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (~.a <: Core.Ops.Bit.Not.t_Output)
  }

let impl: Core.Ops.Bit.t_BitOr t_Random t_Random =
  {
    output = t_Random;
    bitor
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_Random t_Random =
  {
    output = t_Random;
    bitxor
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_Random t_Random =
  {
    output = t_Random;
    bitand
    =
    fun (self: t_Random) (rhs: t_Random) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      let (b: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_Random usize =
  {
    output = t_Random;
    shr
    =
    fun (self: t_Random) (rhs: usize) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a <<. rhs <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_Random usize =
  {
    output = t_Random;
    shl
    =
    fun (self: t_Random) (rhs: usize) ->
      let (a: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a >>. rhs <: Core.Ops.Bit.Shl.t_Output)
  }

let inv_under_impl_125 (self: t_Random) : t_Random =
  let (base: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (inv_under_impl_94 base (max_under_impl_131 <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let pow_felem_under_impl_125 (self exp: t_Random) : t_Random =
  let (base: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_felem_under_impl_94 base
        (Core.Convert.Into.into exp <: t_RandomCanvas)
        (max_under_impl_131 <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let pow_under_impl_125 (self: t_Random) (exp: u128) : t_Random =
  let (base: t_RandomCanvas):t_RandomCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_under_impl_94 base exp (max_under_impl_131 <: t_RandomCanvas)
      <:
      t_RandomCanvas)

let pow2_under_impl_125 (x: usize) : t_Random =
  Core.Convert.Into.into (pow2_under_impl_83 x <: t_RandomCanvas)

let from_byte_seq_be_under_impl_68 (s: a) : t_Random =
  Core.Convert.Into.into (from_be_bytes_under_impl_82 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (fun x -> Secret_integers.declassify_under_impl_2 x <: u8)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (Secret_integers.t_U8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_RandomCanvas)

let from_public_byte_seq_be_under_impl_68 (s: a) : t_Random =
  Core.Convert.Into.into (from_be_bytes_under_impl_82 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter u8)
                    (fun x -> x)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_RandomCanvas)

let to_byte_seq_be_under_impl_68 (self: t_Random) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_be_bytes_under_impl_131 self
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  slice u8)
              <:
              Core.Slice.Iter.t_Iter u8)
            (fun x -> Secret_integers.classify_under_impl_2 x <: Secret_integers.t_U8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> Secret_integers.t_U8))
      <:
      Alloc.Vec.t_Vec Secret_integers.t_U8 Alloc.Alloc.t_Global)

let to_public_byte_seq_be_under_impl_68 (self: t_Random) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_be_bytes_under_impl_131 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_byte_seq_le_under_impl_68 (s: a) : t_Random =
  Core.Convert.Into.into (from_le_bytes_under_impl_82 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (fun x -> Secret_integers.declassify_under_impl_2 x <: u8)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Secret_integers.t_U8)
                    (Secret_integers.t_U8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_RandomCanvas)

let from_public_byte_seq_le_under_impl_68 (s: a) : t_Random =
  Core.Convert.Into.into (from_le_bytes_under_impl_82 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
                (Core.Iter.Traits.Iterator.Iterator.map (Hacspec_lib.Traits.SeqTrait.iter s
                      <:
                      Core.Slice.Iter.t_Iter u8)
                    (fun x -> x)
                  <:
                  Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      t_RandomCanvas)

let to_byte_seq_le_under_impl_68 (self: t_Random) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_le_bytes_under_impl_131 self
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  slice u8)
              <:
              Core.Slice.Iter.t_Iter u8)
            (fun x -> Secret_integers.classify_under_impl_2 x <: Secret_integers.t_U8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> Secret_integers.t_U8))
      <:
      Alloc.Vec.t_Vec Secret_integers.t_U8 Alloc.Alloc.t_Global)

let to_public_byte_seq_le_under_impl_68 (self: t_Random) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_le_bytes_under_impl_131 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_secret_literal_under_impl_68 (x: Secret_integers.t_U128) : t_Random =
  Core.Convert.Into.into (from_literal_under_impl_83 (Secret_integers.declassify_under_impl_126 x
          <:
          u128)
      <:
      t_RandomCanvas)

let impl: Hacspec_lib.Traits.t_NumericCopy t_Random = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_Random = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_Random = {  }

let impl: Hacspec_lib.Traits.t_Integer t_Random =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_131 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_131 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_131 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_131 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_131 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
                      s
                    <:
                    string)
                  "0x"
                  ""
                <:
                Alloc.String.t_String)
            <:
            string));
    get_bit
    =
    (fun (self: t_Random) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &. (Hacspec_lib.Traits.Integer.v_ONE <: t_Random));
    set_bit
    =
    (fun (self: t_Random) (b: t_Random) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_Random)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_Random)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_Random)
                      <:
                      bool))
              then
                let ():Prims.unit =
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO())"

                      <:
                      Rust_primitives.Hax.t_Never)
                in
                ()
            in
            ()
        in
        let tmp1:t_Random = from_literal_under_impl_131 (~.(pub_u128 1sz >>. i <: u128) <: u128) in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_Random) (pos: usize) (y: t_Random) (yi: usize) ->
        let b:t_Random = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_Random) (n: usize) ->
        let _:Prims.unit =
          if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
          then
            let ():Prims.unit =
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                  <:
                  Rust_primitives.Hax.t_Never)
            in
            ()
        in
        ((Core.Clone.Clone.clone self <: t_Random) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_Random) (n: usize) ->
      let _:Prims.unit =
        if ~.(n <. Hacspec_lib.Traits.Integer.v_NUM_BITS <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::NUM_BITS"

                <:
                Rust_primitives.Hax.t_Never)
          in
          ()
      in
      ((Core.Clone.Clone.clone self <: t_Random) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_Random =
  {
    sub_mod = (fun (self: t_Random) (rhs: t_Random) (n: t_Random) -> self -. rhs);
    add_mod = (fun (self: t_Random) (rhs: t_Random) (n: t_Random) -> self +. rhs);
    mul_mod = (fun (self: t_Random) (rhs: t_Random) (n: t_Random) -> self *. rhs);
    pow_mod
    =
    (fun (self: t_Random) (exp: t_Random) (n: t_Random) -> pow_felem_under_impl_125 self exp);
    modulo = (fun (self: t_Random) (n: t_Random) -> self %. n);
    signed_modulo
    =
    (fun (self: t_Random) (n: t_Random) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_Random) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_Random =
  {
    max_val
    =
    (fun  ->
        Core.Convert.Into.into ((max_under_impl_131 <: t_RandomCanvas) -.
            (from_literal_under_impl_83 (pub_u128 1sz) <: t_RandomCanvas)
            <:
            Core.Ops.Arith.Sub.t_Output));
    wrap_add = (fun (self: t_Random) (rhs: t_Random) -> self +. rhs);
    wrap_sub = (fun (self: t_Random) (rhs: t_Random) -> self -. rhs);
    wrap_mul = (fun (self: t_Random) (rhs: t_Random) -> self *. rhs);
    wrap_div = (fun (self: t_Random) (rhs: t_Random) -> self /. rhs);
    exp
    =
    (fun (self: t_Random) (exp: u32) -> pow_under_impl_125 self (Core.Convert.Into.into exp <: u128)
    );
    pow_self = (fun (self: t_Random) (exp: t_Random) -> pow_felem_under_impl_125 self exp);
    divide = (fun (self: t_Random) (rhs: t_Random) -> self /. rhs);
    inv = (fun (self: t_Random) (n: t_Random) -> inv_under_impl_125 self);
    equal = (fun (self: t_Random) (other: t_Random) -> self =. other);
    greater_than = (fun (self: t_Random) (other: t_Random) -> self >. other);
    greater_than_or_equal = (fun (self: t_Random) (other: t_Random) -> self >=. other);
    less_than = (fun (self: t_Random) (other: t_Random) -> self <. other);
    less_than_or_equal = (fun (self: t_Random) (other: t_Random) -> self <=. other);
    not_equal_bm
    =
    (fun (self: t_Random) (other: t_Random) ->
        if self <>. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Random) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    equal_bm
    =
    (fun (self: t_Random) (other: t_Random) ->
        if self =. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Random) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_bm
    =
    (fun (self: t_Random) (other: t_Random) ->
        if self >. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Random) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_or_equal_bm
    =
    (fun (self: t_Random) (other: t_Random) ->
        if self >=. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Random) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_bm
    =
    (fun (self: t_Random) (other: t_Random) ->
        if self <. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Random) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_or_equal_bm
    =
    fun (self: t_Random) (other: t_Random) ->
      if self <=. other
      then
        ((Hacspec_lib.Traits.Integer.v_ONE <: t_Random) >>. (384sz -. 1sz <: usize)
          <:
          Core.Ops.Bit.Shl.t_Output) -.
        (Hacspec_lib.Traits.Integer.v_ONE <: t_Random)
      else Hacspec_lib.Traits.Integer.v_ZERO
  }

let sample_uniform: t_Random = Hacspec_lib.Traits.Integer.v_ONE

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)

let random_oracle_query
      (v_QUERIES:
          Std.Collections.Hash.Map.t_HashMap t_Query t_Random Std.Collections.Hash.Map.t_RandomState
        )
      (q: t_Query)
    : (Std.Collections.Hash.Map.t_HashMap t_Query t_Random Std.Collections.Hash.Map.t_RandomState &
      t_Random) =
  match Std.Collections.Hash.Map.get_under_impl_2 v_QUERIES q with
  | Core.Option.Option_Some r -> Core.Clone.Clone.clone v_QUERIES, Core.Clone.Clone.clone r
  | Core.Option.Option_None  ->
    let r:t_Random = sample_uniform in
    let todo_fresh_var, v_QUERIES_temp:(Core.Option.t_Option t_Random &
      Std.Collections.Hash.Map.t_HashMap t_Query t_Random Std.Collections.Hash.Map.t_RandomState) =
      Std.Collections.Hash.Map.insert_under_impl_2 v_QUERIES q r
    in
    let v_QUERIES:Std.Collections.Hash.Map.t_HashMap t_Query
      t_Random
      Std.Collections.Hash.Map.t_RandomState =
      v_QUERIES_temp
    in
    let _:Core.Option.t_Option t_Random = todo_fresh_var in
    v_QUERIES, r