module Hacspec_ovn.Schnorr
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_GCanvas = {
  f_b:array u8 48sz;
  f_sign:Num_bigint.Bigint.t_Sign;
  f_signed:bool
}

let max_under_impl_15: Core.Ops.Arith.Sub.t_Output =
  ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. 384l <: Core.Ops.Bit.Shl.t_Output) -.
  (Num_traits.Identities.One.one <: Num_bigint.Bigint.t_BigInt)

let max_value_under_impl_15: t_GCanvas =
  Core.Convert.From.from (max_under_impl_15 <: Num_bigint.Bigint.t_BigInt)

let hex_string_to_bytes_under_impl_15 (s: string) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
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

let from_literal_under_impl_15 (x: u128) : t_GCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_15 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type GCanvas"] in
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

let from_signed_literal_under_impl_15 (x: i128) : t_GCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_15 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type GCanvas"] in
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

let pow2_under_impl_15 (x: usize) : t_GCanvas =
  Core.Convert.Into.into ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. x
      <:
      Core.Ops.Bit.Shl.t_Output)

let bit_under_impl_15 (self: t_GCanvas) (i: usize) : bool =
  let _:Prims.unit =
    if
      ~.(i <.
        ((Core.Slice.len_under_impl (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.GCanvas.f_b
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
                                        self.Hacspec_ovn.Schnorr.GCanvas.f_b
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

let impl: Core.Convert.t_From t_GCanvas Num_bigint.Biguint.t_BigUint =
  {
    from
    =
    fun (x: Num_bigint.Biguint.t_BigUint) ->
      Core.Convert.From.from (Core.Convert.From.from x <: Num_bigint.Bigint.t_BigInt)
  }

let impl: Core.Convert.t_From t_GCanvas Num_bigint.Bigint.t_BigInt =
  {
    from
    =
    fun (x: Num_bigint.Bigint.t_BigInt) ->
      let max_value:Num_bigint.Bigint.t_BigInt = max_under_impl_15 in
      let _:Prims.unit =
        if ~.(x <=. max_value <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = [""; " is too large for type GCanvas!"] in
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
                      (Rust_primitives.unsize (let l = [""; " is too large for type GCanvas"] in
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
        Hacspec_ovn.Schnorr.GCanvas.f_b = out;
        Hacspec_ovn.Schnorr.GCanvas.f_sign = sign;
        Hacspec_ovn.Schnorr.GCanvas.f_signed = false
      }
  }

let impl: Core.Default.t_Default t_GCanvas =
  {
    default
    =
    fun  ->
      {
        Hacspec_ovn.Schnorr.GCanvas.f_b = Rust_primitives.Hax.repeat 0uy 48sz;
        Hacspec_ovn.Schnorr.GCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
        Hacspec_ovn.Schnorr.GCanvas.f_signed = false
      }
  }

let impl: Core.Convert.t_Into t_GCanvas Num_bigint.Bigint.t_BigInt =
  {
    into
    =
    fun (self: t_GCanvas) ->
      Num_bigint.Bigint.from_bytes_be_under_impl_24 self.Hacspec_ovn.Schnorr.GCanvas.f_sign
        (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.GCanvas.f_b <: slice u8)
  }

let impl: Core.Convert.t_Into t_GCanvas Num_bigint.Biguint.t_BigUint =
  {
    into
    =
    fun (self: t_GCanvas) ->
      Num_bigint.Biguint.from_bytes_be_under_impl_18 (Rust_primitives.unsize self
              .Hacspec_ovn.Schnorr.GCanvas.f_b
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

let from_hex_under_impl_14 (s: string) : t_GCanvas =
  Core.Convert.Into.into (Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
        (Core.Ops.Deref.Deref.deref (hex_string_to_bytes_under_impl_15 s
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      Num_bigint.Bigint.t_BigInt)

let from_be_bytes_under_impl_14 (v: slice u8) : t_GCanvas =
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
    Hacspec_ovn.Schnorr.GCanvas.f_b = repr;
    Hacspec_ovn.Schnorr.GCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
    Hacspec_ovn.Schnorr.GCanvas.f_signed = false
  }

let from_le_bytes_under_impl_14 (v: slice u8) : t_GCanvas =
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

let to_be_bytes_under_impl_14 (self: t_GCanvas) : array u8 48sz =
  self.Hacspec_ovn.Schnorr.GCanvas.f_b

let to_le_bytes_under_impl_14 (self: t_GCanvas) : array u8 48sz =
  let x:Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
      (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.GCanvas.f_b <: slice u8)
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

let comp_eq_under_impl_14 (self rhs: t_GCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a =. b
  then
    let one:t_GCanvas = from_literal_under_impl_15 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_ne_under_impl_14 (self rhs: t_GCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <>. b
  then
    let one:t_GCanvas = from_literal_under_impl_15 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gte_under_impl_14 (self rhs: t_GCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >=. b
  then
    let one:t_GCanvas = from_literal_under_impl_15 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gt_under_impl_14 (self rhs: t_GCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >. b
  then
    let one:t_GCanvas = from_literal_under_impl_15 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lte_under_impl_14 (self rhs: t_GCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <=. b
  then
    let one:t_GCanvas = from_literal_under_impl_15 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lt_under_impl_14 (self rhs: t_GCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <. b
  then
    let one:t_GCanvas = from_literal_under_impl_15 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let inv_under_impl_26 (self modval: t_GCanvas) : t_GCanvas =
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

let pow_felem_under_impl_26 (self exp modval: t_GCanvas) : t_GCanvas =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into exp in
  let (m: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into modval in
  let (c: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.modpow_under_impl_24 a b m
  in
  Core.Convert.Into.into c

let pow_under_impl_26 (self: t_GCanvas) (exp: u128) (modval: t_GCanvas) : t_GCanvas =
  pow_felem_under_impl_26 self
    (Core.Convert.Into.into (Core.Convert.From.from exp <: Num_bigint.Bigint.t_BigInt) <: t_GCanvas)
    modval

let rem_under_impl_26 (self n: t_GCanvas) : Core.Ops.Arith.Rem.t_Output = self %. n

let impl: Core.Ops.Arith.t_Add t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    add
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Add.t_Output = a +. b in
      let _:Prims.unit =
        if c >. (max_under_impl_15 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded addition overflow for type GCanvas"]
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

let impl: Core.Ops.Arith.t_Sub t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    sub
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Sub.t_Output =
        if self.Hacspec_ovn.Schnorr.GCanvas.f_signed
        then a -. b
        else
          Core.Option.unwrap_or_else_under_impl (Num_bigint.Bigint.checked_sub_under_impl_24 a b
              <:
              Core.Option.t_Option Num_bigint.Bigint.t_BigInt)
            (fun  ->
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                          (Rust_primitives.unsize (let l =
                                  ["bounded substraction underflow for type GCanvas"]
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

let impl: Core.Ops.Arith.t_Mul t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    mul
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Mul.t_Output = a *. b in
      let _:Prims.unit =
        if c >. (max_under_impl_15 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded multiplication overflow for type GCanvas"]
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

let impl: Core.Ops.Arith.t_Div t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    div
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type GCanvas"] in
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

let impl: Core.Ops.Arith.t_Rem t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    rem
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type GCanvas"] in
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

let impl: Core.Ops.Bit.t_Not t_GCanvas =
  {
    output = t_GCanvas;
    not
    =
    fun (self: t_GCanvas) ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
          <:
          Rust_primitives.Hax.t_Never)
  }

let impl: Core.Ops.Bit.t_BitOr t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    bitor
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    bitxor
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_GCanvas t_GCanvas =
  {
    output = t_GCanvas;
    bitand
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_GCanvas usize =
  {
    output = t_GCanvas;
    shr
    =
    fun (self: t_GCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a <<. b <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_GCanvas usize =
  {
    output = t_GCanvas;
    shl
    =
    fun (self: t_GCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a >>. b <: Core.Ops.Bit.Shl.t_Output)
  }

let impl: Core.Cmp.t_PartialEq t_GCanvas t_GCanvas =
  {
    eq
    =
    fun (self: t_GCanvas) (rhs: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      a =. b
  }

let impl: Core.Cmp.t_Eq t_GCanvas = {  }

let impl: Core.Cmp.t_PartialOrd t_GCanvas t_GCanvas =
  {
    partial_cmp
    =
    fun (self: t_GCanvas) (other: t_GCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into other
      in
      Core.Cmp.PartialOrd.partial_cmp a b
  }

let impl: Core.Cmp.t_Ord t_GCanvas =
  {
    cmp
    =
    fun (self: t_GCanvas) (other: t_GCanvas) ->
      Core.Option.unwrap_under_impl (Core.Cmp.PartialOrd.partial_cmp self other
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering)
  }

let from_byte_seq_be_under_impl_7 (s: a) : t_GCanvas =
  from_be_bytes_under_impl_14 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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

let from_public_byte_seq_be_under_impl_7 (s: a) : t_GCanvas =
  from_be_bytes_under_impl_14 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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

let to_byte_seq_be_under_impl_7 (self: t_GCanvas) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_14 self
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

let impl: Hacspec_lib.Traits.t_NumericCopy t_GCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_GCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_GCanvas = {  }

let impl: Hacspec_lib.Traits.t_Integer t_GCanvas =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_15 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_15 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_15 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_15 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_14 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
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
    (fun (self: t_GCanvas) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &. (Hacspec_lib.Traits.Integer.v_ONE <: t_GCanvas)
    );
    set_bit
    =
    (fun (self: t_GCanvas) (b: t_GCanvas) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_GCanvas)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_GCanvas)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_GCanvas)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_GCanvas)
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
        let tmp1:t_GCanvas = from_literal_under_impl_15 (~.(pub_u128 1sz >>. i <: u128) <: u128) in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_GCanvas) (pos: usize) (y: t_GCanvas) (yi: usize) ->
        let b:t_GCanvas = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_GCanvas) (n: usize) ->
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
        ((Core.Clone.Clone.clone self <: t_GCanvas) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_GCanvas) (n: usize) ->
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
      ((Core.Clone.Clone.clone self <: t_GCanvas) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_GCanvas =
  {
    sub_mod
    =
    (fun (self: t_GCanvas) (rhs: t_GCanvas) (n: t_GCanvas) ->
        (self -. rhs <: Core.Ops.Arith.Sub.t_Output) %. n);
    add_mod
    =
    (fun (self: t_GCanvas) (rhs: t_GCanvas) (n: t_GCanvas) ->
        (self +. rhs <: Core.Ops.Arith.Add.t_Output) %. n);
    mul_mod
    =
    (fun (self: t_GCanvas) (rhs: t_GCanvas) (n: t_GCanvas) ->
        (self *. rhs <: Core.Ops.Arith.Mul.t_Output) %. n);
    pow_mod
    =
    (fun (self: t_GCanvas) (exp: t_GCanvas) (n: t_GCanvas) -> pow_felem_under_impl_26 self exp n);
    modulo = (fun (self: t_GCanvas) (n: t_GCanvas) -> self %. n);
    signed_modulo
    =
    (fun (self: t_GCanvas) (n: t_GCanvas) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_GCanvas) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_GCanvas =
  {
    max_val = (fun  -> max_value_under_impl_15);
    wrap_add = (fun (self: t_GCanvas) (rhs: t_GCanvas) -> self +. rhs);
    wrap_sub = (fun (self: t_GCanvas) (rhs: t_GCanvas) -> self -. rhs);
    wrap_mul = (fun (self: t_GCanvas) (rhs: t_GCanvas) -> self *. rhs);
    wrap_div = (fun (self: t_GCanvas) (rhs: t_GCanvas) -> self /. rhs);
    exp
    =
    (fun (self: t_GCanvas) (exp: u32) ->
        pow_under_impl_26 self
          (Core.Convert.Into.into exp <: u128)
          (Hacspec_lib.Traits.Numeric.max_val <: t_GCanvas));
    pow_self
    =
    (fun (self: t_GCanvas) (exp: t_GCanvas) ->
        pow_felem_under_impl_26 self
          (Core.Convert.Into.into exp <: t_GCanvas)
          (Hacspec_lib.Traits.Numeric.max_val <: t_GCanvas));
    divide = (fun (self: t_GCanvas) (rhs: t_GCanvas) -> self /. rhs);
    inv = (fun (self: t_GCanvas) (n: t_GCanvas) -> inv_under_impl_26 self n);
    equal = (fun (self: t_GCanvas) (other: t_GCanvas) -> self =. other);
    greater_than = (fun (self: t_GCanvas) (other: t_GCanvas) -> self >. other);
    greater_than_or_equal = (fun (self: t_GCanvas) (other: t_GCanvas) -> self >=. other);
    less_than = (fun (self: t_GCanvas) (other: t_GCanvas) -> self <. other);
    less_than_or_equal = (fun (self: t_GCanvas) (other: t_GCanvas) -> self >=. other);
    not_equal_bm
    =
    (fun (self: t_GCanvas) (other: t_GCanvas) ->
        if ~.(Hacspec_lib.Traits.Numeric.equal self other <: bool)
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_15 (pub_u128 0sz));
    equal_bm
    =
    (fun (self: t_GCanvas) (other: t_GCanvas) ->
        if Hacspec_lib.Traits.Numeric.equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_15 (pub_u128 0sz));
    greater_than_bm
    =
    (fun (self: t_GCanvas) (other: t_GCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_15 (pub_u128 0sz));
    greater_than_or_equal_bm
    =
    (fun (self: t_GCanvas) (other: t_GCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than_or_equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_15 (pub_u128 0sz));
    less_than_bm
    =
    (fun (self: t_GCanvas) (other: t_GCanvas) ->
        if Hacspec_lib.Traits.Numeric.less_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_15 (pub_u128 0sz));
    less_than_or_equal_bm
    =
    fun (self: t_GCanvas) (other: t_GCanvas) ->
      if Hacspec_lib.Traits.Numeric.less_than_or_equal self other
      then Hacspec_lib.Traits.Numeric.max_val
      else from_literal_under_impl_15 (pub_u128 0sz)
  }

type t_G = | G : t_GCanvas -> t_G

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

let impl: Core.Convert.t_From t_G t_GCanvas =
  {
    from
    =
    fun (x: t_GCanvas) ->
      G
      (rem_under_impl_26 x
          (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_GCanvas))
  }

let impl: Core.Convert.t_Into t_G t_GCanvas =
  { into = fun (self: t_G) -> self.Hacspec_ovn.Schnorr.G.0 }

let from_canvas_under_impl_63 (x: t_GCanvas) : t_G =
  G
  (rem_under_impl_26 x
      (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_GCanvas))

let into_canvas_under_impl_63 (self: t_G) : t_GCanvas = self.Hacspec_ovn.Schnorr.G.0

let max_under_impl_63: t_GCanvas =
  from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

let declassify_under_impl_63 (self: t_G) : Num_bigint.Bigint.t_BigInt =
  let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into a

let from_hex_under_impl_63 (s: string) : t_G =
  Core.Convert.Into.into (from_hex_under_impl_14 s <: t_GCanvas)

let from_be_bytes_under_impl_63 (v: slice u8) : t_G =
  Core.Convert.Into.into (from_be_bytes_under_impl_14 v <: t_GCanvas)

let to_be_bytes_under_impl_63 (self: t_G) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_14 (Core.Convert.Into.into
                self
              <:
              t_GCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let from_le_bytes_under_impl_63 (v: slice u8) : t_G =
  Core.Convert.Into.into (from_le_bytes_under_impl_14 v <: t_GCanvas)

let to_le_bytes_under_impl_63 (self: t_G) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_le_bytes_under_impl_14 (Core.Convert.Into.into
                self
              <:
              t_GCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let bit_under_impl_63 (self: t_G) (i: usize) : bool =
  bit_under_impl_15 (Core.Convert.Into.into self <: t_GCanvas) i

let from_literal_under_impl_63 (x: u128) : t_G =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_63 <: t_GCanvas) <: Num_bigint.Biguint.t_BigUint)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type G"] in
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
  G (Core.Convert.Into.into big_x)

let from_signed_literal_under_impl_63 (x: i128) : t_G =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_63 <: t_GCanvas) <: Num_bigint.Biguint.t_BigUint)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type G"] in
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
  G (Core.Convert.Into.into big_x)

let comp_eq_under_impl_63 (self rhs: t_G) : t_G =
  let (x: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_eq_under_impl_14 x (Core.Convert.Into.into rhs <: t_GCanvas)
      <:
      t_GCanvas)

let comp_ne_under_impl_63 (self rhs: t_G) : t_G =
  let (x: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_ne_under_impl_14 x (Core.Convert.Into.into rhs <: t_GCanvas)
      <:
      t_GCanvas)

let comp_gte_under_impl_63 (self rhs: t_G) : t_G =
  let (x: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gte_under_impl_14 x (Core.Convert.Into.into rhs <: t_GCanvas)
      <:
      t_GCanvas)

let comp_gt_under_impl_63 (self rhs: t_G) : t_G =
  let (x: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gt_under_impl_14 x (Core.Convert.Into.into rhs <: t_GCanvas)
      <:
      t_GCanvas)

let comp_lte_under_impl_63 (self rhs: t_G) : t_G =
  let (x: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lte_under_impl_14 x (Core.Convert.Into.into rhs <: t_GCanvas)
      <:
      t_GCanvas)

let comp_lt_under_impl_63 (self rhs: t_G) : t_G =
  let (x: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lt_under_impl_14 x (Core.Convert.Into.into rhs <: t_GCanvas)
      <:
      t_GCanvas)

let neg_under_impl_63 (self: t_G) : t_G =
  let (mod_val: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_GCanvas)
  in
  let (s: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  let (s: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into s in
  let (result: t_GCanvas):t_GCanvas =
    Core.Convert.Into.into (mod_val -. s <: Core.Ops.Arith.Sub.t_Output)
  in
  Core.Convert.Into.into result

let impl: Core.Cmp.t_PartialOrd t_G t_G =
  {
    partial_cmp
    =
    fun (self: t_G) (other: t_G) -> Core.Option.Option_Some (Core.Cmp.Ord.cmp self other)
  }

let impl: Core.Cmp.t_Ord t_G =
  {
    cmp
    =
    fun (self: t_G) (other: t_G) ->
      Core.Cmp.Ord.cmp self.Hacspec_ovn.Schnorr.G.0 other.Hacspec_ovn.Schnorr.G.0
  }

let impl: Core.Cmp.t_PartialEq t_G t_G =
  {
    eq
    =
    fun (self: t_G) (other: t_G) -> self.Hacspec_ovn.Schnorr.G.0 =. other.Hacspec_ovn.Schnorr.G.0
  }

let impl: Core.Cmp.t_Eq t_G = {  }

let impl: Core.Ops.Arith.t_Add t_G t_G =
  {
    output = t_G;
    add
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Add.t_Output = a +. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_GCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_GCanvas):t_GCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Sub t_G t_G =
  {
    output = t_G;
    sub
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_GCanvas)
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
      let (d: t_GCanvas):t_GCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Mul t_G t_G =
  {
    output = t_G;
    mul
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Mul.t_Output = a *. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_GCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_GCanvas):t_GCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Div t_G t_G =
  { output = t_G; div = fun (self: t_G) (rhs: t_G) -> self *. (inv_under_impl_57 rhs <: t_G) }

let impl: Core.Ops.Arith.t_Rem t_G t_G =
  {
    output = t_G;
    rem
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = a %. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_14 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_GCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_GCanvas):t_GCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Bit.t_Not t_G =
  {
    output = t_G;
    not
    =
    fun (self: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (~.a <: Core.Ops.Bit.Not.t_Output)
  }

let impl: Core.Ops.Bit.t_BitOr t_G t_G =
  {
    output = t_G;
    bitor
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_G t_G =
  {
    output = t_G;
    bitxor
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_G t_G =
  {
    output = t_G;
    bitand
    =
    fun (self: t_G) (rhs: t_G) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      let (b: t_GCanvas):t_GCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_G usize =
  {
    output = t_G;
    shr
    =
    fun (self: t_G) (rhs: usize) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a <<. rhs <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_G usize =
  {
    output = t_G;
    shl
    =
    fun (self: t_G) (rhs: usize) ->
      let (a: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a >>. rhs <: Core.Ops.Bit.Shl.t_Output)
  }

let inv_under_impl_57 (self: t_G) : t_G =
  let (base: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (inv_under_impl_26 base (max_under_impl_63 <: t_GCanvas) <: t_GCanvas)

let pow_felem_under_impl_57 (self exp: t_G) : t_G =
  let (base: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_felem_under_impl_26 base
        (Core.Convert.Into.into exp <: t_GCanvas)
        (max_under_impl_63 <: t_GCanvas)
      <:
      t_GCanvas)

let pow_under_impl_57 (self: t_G) (exp: u128) : t_G =
  let (base: t_GCanvas):t_GCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_under_impl_26 base exp (max_under_impl_63 <: t_GCanvas) <: t_GCanvas)

let pow2_under_impl_57 (x: usize) : t_G = Core.Convert.Into.into (pow2_under_impl_15 x <: t_GCanvas)

let from_byte_seq_be_under_impl (s: a) : t_G =
  Core.Convert.Into.into (from_be_bytes_under_impl_14 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_GCanvas)

let from_public_byte_seq_be_under_impl (s: a) : t_G =
  Core.Convert.Into.into (from_be_bytes_under_impl_14 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_GCanvas)

let to_byte_seq_be_under_impl (self: t_G) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_be_bytes_under_impl_63 self
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

let to_public_byte_seq_be_under_impl (self: t_G) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_be_bytes_under_impl_63 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_byte_seq_le_under_impl (s: a) : t_G =
  Core.Convert.Into.into (from_le_bytes_under_impl_14 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_GCanvas)

let from_public_byte_seq_le_under_impl (s: a) : t_G =
  Core.Convert.Into.into (from_le_bytes_under_impl_14 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_GCanvas)

let to_byte_seq_le_under_impl (self: t_G) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_le_bytes_under_impl_63 self
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

let to_public_byte_seq_le_under_impl (self: t_G) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_le_bytes_under_impl_63 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_secret_literal_under_impl (x: Secret_integers.t_U128) : t_G =
  Core.Convert.Into.into (from_literal_under_impl_15 (Secret_integers.declassify_under_impl_126 x
          <:
          u128)
      <:
      t_GCanvas)

let impl: Hacspec_lib.Traits.t_NumericCopy t_G = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_G = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_G = {  }

let impl: Hacspec_lib.Traits.t_Integer t_G =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_63 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_63 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_63 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_63 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_63 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
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
    (fun (self: t_G) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &. (Hacspec_lib.Traits.Integer.v_ONE <: t_G));
    set_bit
    =
    (fun (self: t_G) (b: t_G) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_G)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_G)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_G)
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
        let tmp1:t_G = from_literal_under_impl_63 (~.(pub_u128 1sz >>. i <: u128) <: u128) in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_G) (pos: usize) (y: t_G) (yi: usize) ->
        let b:t_G = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_G) (n: usize) ->
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
        ((Core.Clone.Clone.clone self <: t_G) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_G) (n: usize) ->
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
      ((Core.Clone.Clone.clone self <: t_G) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_G =
  {
    sub_mod = (fun (self: t_G) (rhs: t_G) (n: t_G) -> self -. rhs);
    add_mod = (fun (self: t_G) (rhs: t_G) (n: t_G) -> self +. rhs);
    mul_mod = (fun (self: t_G) (rhs: t_G) (n: t_G) -> self *. rhs);
    pow_mod = (fun (self: t_G) (exp: t_G) (n: t_G) -> pow_felem_under_impl_57 self exp);
    modulo = (fun (self: t_G) (n: t_G) -> self %. n);
    signed_modulo = (fun (self: t_G) (n: t_G) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_G) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_G =
  {
    max_val
    =
    (fun  ->
        Core.Convert.Into.into ((max_under_impl_63 <: t_GCanvas) -.
            (from_literal_under_impl_15 (pub_u128 1sz) <: t_GCanvas)
            <:
            Core.Ops.Arith.Sub.t_Output));
    wrap_add = (fun (self: t_G) (rhs: t_G) -> self +. rhs);
    wrap_sub = (fun (self: t_G) (rhs: t_G) -> self -. rhs);
    wrap_mul = (fun (self: t_G) (rhs: t_G) -> self *. rhs);
    wrap_div = (fun (self: t_G) (rhs: t_G) -> self /. rhs);
    exp
    =
    (fun (self: t_G) (exp: u32) -> pow_under_impl_57 self (Core.Convert.Into.into exp <: u128));
    pow_self = (fun (self: t_G) (exp: t_G) -> pow_felem_under_impl_57 self exp);
    divide = (fun (self: t_G) (rhs: t_G) -> self /. rhs);
    inv = (fun (self: t_G) (n: t_G) -> inv_under_impl_57 self);
    equal = (fun (self: t_G) (other: t_G) -> self =. other);
    greater_than = (fun (self: t_G) (other: t_G) -> self >. other);
    greater_than_or_equal = (fun (self: t_G) (other: t_G) -> self >=. other);
    less_than = (fun (self: t_G) (other: t_G) -> self <. other);
    less_than_or_equal = (fun (self: t_G) (other: t_G) -> self <=. other);
    not_equal_bm
    =
    (fun (self: t_G) (other: t_G) ->
        if self <>. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_G) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    equal_bm
    =
    (fun (self: t_G) (other: t_G) ->
        if self =. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_G) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_bm
    =
    (fun (self: t_G) (other: t_G) ->
        if self >. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_G) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_or_equal_bm
    =
    (fun (self: t_G) (other: t_G) ->
        if self >=. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_G) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_bm
    =
    (fun (self: t_G) (other: t_G) ->
        if self <. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_G) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_or_equal_bm
    =
    fun (self: t_G) (other: t_G) ->
      if self <=. other
      then
        ((Hacspec_lib.Traits.Integer.v_ONE <: t_G) >>. (384sz -. 1sz <: usize)
          <:
          Core.Ops.Bit.Shl.t_Output) -.
        (Hacspec_lib.Traits.Integer.v_ONE <: t_G)
      else Hacspec_lib.Traits.Integer.v_ZERO
  }

type t_QCanvas = {
  f_b:array u8 48sz;
  f_sign:Num_bigint.Bigint.t_Sign;
  f_signed:bool
}

let max_under_impl_82: Core.Ops.Arith.Sub.t_Output =
  ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. 384l <: Core.Ops.Bit.Shl.t_Output) -.
  (Num_traits.Identities.One.one <: Num_bigint.Bigint.t_BigInt)

let max_value_under_impl_82: t_QCanvas =
  Core.Convert.From.from (max_under_impl_82 <: Num_bigint.Bigint.t_BigInt)

let hex_string_to_bytes_under_impl_82 (s: string) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
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

let from_literal_under_impl_82 (x: u128) : t_QCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_82 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type QCanvas"] in
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

let from_signed_literal_under_impl_82 (x: i128) : t_QCanvas =
  let big_x:Num_bigint.Bigint.t_BigInt = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_82 <: Num_bigint.Bigint.t_BigInt)
        <:
        Num_bigint.Bigint.t_BigInt)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type QCanvas"] in
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

let pow2_under_impl_82 (x: usize) : t_QCanvas =
  Core.Convert.Into.into ((Core.Convert.From.from 1ul <: Num_bigint.Bigint.t_BigInt) >>. x
      <:
      Core.Ops.Bit.Shl.t_Output)

let bit_under_impl_82 (self: t_QCanvas) (i: usize) : bool =
  let _:Prims.unit =
    if
      ~.(i <.
        ((Core.Slice.len_under_impl (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.QCanvas.f_b
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
                                        self.Hacspec_ovn.Schnorr.QCanvas.f_b
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

let impl: Core.Convert.t_From t_QCanvas Num_bigint.Biguint.t_BigUint =
  {
    from
    =
    fun (x: Num_bigint.Biguint.t_BigUint) ->
      Core.Convert.From.from (Core.Convert.From.from x <: Num_bigint.Bigint.t_BigInt)
  }

let impl: Core.Convert.t_From t_QCanvas Num_bigint.Bigint.t_BigInt =
  {
    from
    =
    fun (x: Num_bigint.Bigint.t_BigInt) ->
      let max_value:Num_bigint.Bigint.t_BigInt = max_under_impl_82 in
      let _:Prims.unit =
        if ~.(x <=. max_value <: bool)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = [""; " is too large for type QCanvas!"] in
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
                      (Rust_primitives.unsize (let l = [""; " is too large for type QCanvas"] in
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
        Hacspec_ovn.Schnorr.QCanvas.f_b = out;
        Hacspec_ovn.Schnorr.QCanvas.f_sign = sign;
        Hacspec_ovn.Schnorr.QCanvas.f_signed = false
      }
  }

let impl: Core.Default.t_Default t_QCanvas =
  {
    default
    =
    fun  ->
      {
        Hacspec_ovn.Schnorr.QCanvas.f_b = Rust_primitives.Hax.repeat 0uy 48sz;
        Hacspec_ovn.Schnorr.QCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
        Hacspec_ovn.Schnorr.QCanvas.f_signed = false
      }
  }

let impl: Core.Convert.t_Into t_QCanvas Num_bigint.Bigint.t_BigInt =
  {
    into
    =
    fun (self: t_QCanvas) ->
      Num_bigint.Bigint.from_bytes_be_under_impl_24 self.Hacspec_ovn.Schnorr.QCanvas.f_sign
        (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.QCanvas.f_b <: slice u8)
  }

let impl: Core.Convert.t_Into t_QCanvas Num_bigint.Biguint.t_BigUint =
  {
    into
    =
    fun (self: t_QCanvas) ->
      Num_bigint.Biguint.from_bytes_be_under_impl_18 (Rust_primitives.unsize self
              .Hacspec_ovn.Schnorr.QCanvas.f_b
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

let from_hex_under_impl_81 (s: string) : t_QCanvas =
  Core.Convert.Into.into (Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
        (Core.Ops.Deref.Deref.deref (hex_string_to_bytes_under_impl_82 s
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          <:
          slice u8)
      <:
      Num_bigint.Bigint.t_BigInt)

let from_be_bytes_under_impl_81 (v: slice u8) : t_QCanvas =
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
    Hacspec_ovn.Schnorr.QCanvas.f_b = repr;
    Hacspec_ovn.Schnorr.QCanvas.f_sign = Num_bigint.Bigint.Sign_Plus;
    Hacspec_ovn.Schnorr.QCanvas.f_signed = false
  }

let from_le_bytes_under_impl_81 (v: slice u8) : t_QCanvas =
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

let to_be_bytes_under_impl_81 (self: t_QCanvas) : array u8 48sz =
  self.Hacspec_ovn.Schnorr.QCanvas.f_b

let to_le_bytes_under_impl_81 (self: t_QCanvas) : array u8 48sz =
  let x:Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.from_bytes_be_under_impl_24 Num_bigint.Bigint.Sign_Plus
      (Rust_primitives.unsize self.Hacspec_ovn.Schnorr.QCanvas.f_b <: slice u8)
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

let comp_eq_under_impl_81 (self rhs: t_QCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a =. b
  then
    let one:t_QCanvas = from_literal_under_impl_82 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_ne_under_impl_81 (self rhs: t_QCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <>. b
  then
    let one:t_QCanvas = from_literal_under_impl_82 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gte_under_impl_81 (self rhs: t_QCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >=. b
  then
    let one:t_QCanvas = from_literal_under_impl_82 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_gt_under_impl_81 (self rhs: t_QCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a >. b
  then
    let one:t_QCanvas = from_literal_under_impl_82 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lte_under_impl_81 (self rhs: t_QCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <=. b
  then
    let one:t_QCanvas = from_literal_under_impl_82 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let comp_lt_under_impl_81 (self rhs: t_QCanvas) : Core.Ops.Arith.Sub.t_Output =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
  if a <. b
  then
    let one:t_QCanvas = from_literal_under_impl_82 (pub_u128 1sz) in
    (one >>. (384sz -. 1sz <: usize) <: Core.Ops.Bit.Shl.t_Output) -. one
  else Core.Default.Default.v_default

let inv_under_impl_93 (self modval: t_QCanvas) : t_QCanvas =
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

let pow_felem_under_impl_93 (self exp modval: t_QCanvas) : t_QCanvas =
  let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into self in
  let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into exp in
  let (m: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into modval in
  let (c: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Num_bigint.Bigint.modpow_under_impl_24 a b m
  in
  Core.Convert.Into.into c

let pow_under_impl_93 (self: t_QCanvas) (exp: u128) (modval: t_QCanvas) : t_QCanvas =
  pow_felem_under_impl_93 self
    (Core.Convert.Into.into (Core.Convert.From.from exp <: Num_bigint.Bigint.t_BigInt) <: t_QCanvas)
    modval

let rem_under_impl_93 (self n: t_QCanvas) : Core.Ops.Arith.Rem.t_Output = self %. n

let impl: Core.Ops.Arith.t_Add t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    add
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Add.t_Output = a +. b in
      let _:Prims.unit =
        if c >. (max_under_impl_82 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded addition overflow for type QCanvas"]
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

let impl: Core.Ops.Arith.t_Sub t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    sub
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Sub.t_Output =
        if self.Hacspec_ovn.Schnorr.QCanvas.f_signed
        then a -. b
        else
          Core.Option.unwrap_or_else_under_impl (Num_bigint.Bigint.checked_sub_under_impl_24 a b
              <:
              Core.Option.t_Option Num_bigint.Bigint.t_BigInt)
            (fun  ->
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                          (Rust_primitives.unsize (let l =
                                  ["bounded substraction underflow for type QCanvas"]
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

let impl: Core.Ops.Arith.t_Mul t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    mul
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let c:Core.Ops.Arith.Mul.t_Output = a *. b in
      let _:Prims.unit =
        if c >. (max_under_impl_82 <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l =
                              ["bounded multiplication overflow for type QCanvas"]
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

let impl: Core.Ops.Arith.t_Div t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    div
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type QCanvas"] in
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

let impl: Core.Ops.Arith.t_Rem t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    rem
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      let _:Prims.unit =
        if b =. (Num_traits.Identities.Zero.zero <: Num_bigint.Bigint.t_BigInt)
        then
          let ():Prims.unit =
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2
                      (Rust_primitives.unsize (let l = ["dividing by zero in type QCanvas"] in
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

let impl: Core.Ops.Bit.t_Not t_QCanvas =
  {
    output = t_QCanvas;
    not
    =
    fun (self: t_QCanvas) ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
          <:
          Rust_primitives.Hax.t_Never)
  }

let impl: Core.Ops.Bit.t_BitOr t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    bitor
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    bitxor
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_QCanvas t_QCanvas =
  {
    output = t_QCanvas;
    bitand
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_QCanvas usize =
  {
    output = t_QCanvas;
    shr
    =
    fun (self: t_QCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a <<. b <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_QCanvas usize =
  {
    output = t_QCanvas;
    shl
    =
    fun (self: t_QCanvas) (rhs: usize) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let b:usize = rhs in
      Core.Convert.Into.into (a >>. b <: Core.Ops.Bit.Shl.t_Output)
  }

let impl: Core.Cmp.t_PartialEq t_QCanvas t_QCanvas =
  {
    eq
    =
    fun (self: t_QCanvas) (rhs: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into rhs in
      a =. b
  }

let impl: Core.Cmp.t_Eq t_QCanvas = {  }

let impl: Core.Cmp.t_PartialOrd t_QCanvas t_QCanvas =
  {
    partial_cmp
    =
    fun (self: t_QCanvas) (other: t_QCanvas) ->
      let (a: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into self
      in
      let (b: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
        Core.Convert.Into.into other
      in
      Core.Cmp.PartialOrd.partial_cmp a b
  }

let impl: Core.Cmp.t_Ord t_QCanvas =
  {
    cmp
    =
    fun (self: t_QCanvas) (other: t_QCanvas) ->
      Core.Option.unwrap_under_impl (Core.Cmp.PartialOrd.partial_cmp self other
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering)
  }

let from_byte_seq_be_under_impl_74 (s: a) : t_QCanvas =
  from_be_bytes_under_impl_81 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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

let from_public_byte_seq_be_under_impl_74 (s: a) : t_QCanvas =
  from_be_bytes_under_impl_81 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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

let to_byte_seq_be_under_impl_74 (self: t_QCanvas) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_81 self
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

let impl: Hacspec_lib.Traits.t_NumericCopy t_QCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_QCanvas = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_QCanvas = {  }

let impl: Hacspec_lib.Traits.t_Integer t_QCanvas =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_82 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_82 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_82 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_82 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_81 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
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
    (fun (self: t_QCanvas) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &. (Hacspec_lib.Traits.Integer.v_ONE <: t_QCanvas)
    );
    set_bit
    =
    (fun (self: t_QCanvas) (b: t_QCanvas) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_QCanvas)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_QCanvas)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_QCanvas)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_QCanvas)
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
        let tmp1:t_QCanvas = from_literal_under_impl_82 (~.(pub_u128 1sz >>. i <: u128) <: u128) in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_QCanvas) (pos: usize) (y: t_QCanvas) (yi: usize) ->
        let b:t_QCanvas = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_QCanvas) (n: usize) ->
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
        ((Core.Clone.Clone.clone self <: t_QCanvas) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_QCanvas) (n: usize) ->
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
      ((Core.Clone.Clone.clone self <: t_QCanvas) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_QCanvas =
  {
    sub_mod
    =
    (fun (self: t_QCanvas) (rhs: t_QCanvas) (n: t_QCanvas) ->
        (self -. rhs <: Core.Ops.Arith.Sub.t_Output) %. n);
    add_mod
    =
    (fun (self: t_QCanvas) (rhs: t_QCanvas) (n: t_QCanvas) ->
        (self +. rhs <: Core.Ops.Arith.Add.t_Output) %. n);
    mul_mod
    =
    (fun (self: t_QCanvas) (rhs: t_QCanvas) (n: t_QCanvas) ->
        (self *. rhs <: Core.Ops.Arith.Mul.t_Output) %. n);
    pow_mod
    =
    (fun (self: t_QCanvas) (exp: t_QCanvas) (n: t_QCanvas) -> pow_felem_under_impl_93 self exp n);
    modulo = (fun (self: t_QCanvas) (n: t_QCanvas) -> self %. n);
    signed_modulo
    =
    (fun (self: t_QCanvas) (n: t_QCanvas) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_QCanvas) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_QCanvas =
  {
    max_val = (fun  -> max_value_under_impl_82);
    wrap_add = (fun (self: t_QCanvas) (rhs: t_QCanvas) -> self +. rhs);
    wrap_sub = (fun (self: t_QCanvas) (rhs: t_QCanvas) -> self -. rhs);
    wrap_mul = (fun (self: t_QCanvas) (rhs: t_QCanvas) -> self *. rhs);
    wrap_div = (fun (self: t_QCanvas) (rhs: t_QCanvas) -> self /. rhs);
    exp
    =
    (fun (self: t_QCanvas) (exp: u32) ->
        pow_under_impl_93 self
          (Core.Convert.Into.into exp <: u128)
          (Hacspec_lib.Traits.Numeric.max_val <: t_QCanvas));
    pow_self
    =
    (fun (self: t_QCanvas) (exp: t_QCanvas) ->
        pow_felem_under_impl_93 self
          (Core.Convert.Into.into exp <: t_QCanvas)
          (Hacspec_lib.Traits.Numeric.max_val <: t_QCanvas));
    divide = (fun (self: t_QCanvas) (rhs: t_QCanvas) -> self /. rhs);
    inv = (fun (self: t_QCanvas) (n: t_QCanvas) -> inv_under_impl_93 self n);
    equal = (fun (self: t_QCanvas) (other: t_QCanvas) -> self =. other);
    greater_than = (fun (self: t_QCanvas) (other: t_QCanvas) -> self >. other);
    greater_than_or_equal = (fun (self: t_QCanvas) (other: t_QCanvas) -> self >=. other);
    less_than = (fun (self: t_QCanvas) (other: t_QCanvas) -> self <. other);
    less_than_or_equal = (fun (self: t_QCanvas) (other: t_QCanvas) -> self >=. other);
    not_equal_bm
    =
    (fun (self: t_QCanvas) (other: t_QCanvas) ->
        if ~.(Hacspec_lib.Traits.Numeric.equal self other <: bool)
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_82 (pub_u128 0sz));
    equal_bm
    =
    (fun (self: t_QCanvas) (other: t_QCanvas) ->
        if Hacspec_lib.Traits.Numeric.equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_82 (pub_u128 0sz));
    greater_than_bm
    =
    (fun (self: t_QCanvas) (other: t_QCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_82 (pub_u128 0sz));
    greater_than_or_equal_bm
    =
    (fun (self: t_QCanvas) (other: t_QCanvas) ->
        if Hacspec_lib.Traits.Numeric.greater_than_or_equal self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_82 (pub_u128 0sz));
    less_than_bm
    =
    (fun (self: t_QCanvas) (other: t_QCanvas) ->
        if Hacspec_lib.Traits.Numeric.less_than self other
        then Hacspec_lib.Traits.Numeric.max_val
        else from_literal_under_impl_82 (pub_u128 0sz));
    less_than_or_equal_bm
    =
    fun (self: t_QCanvas) (other: t_QCanvas) ->
      if Hacspec_lib.Traits.Numeric.less_than_or_equal self other
      then Hacspec_lib.Traits.Numeric.max_val
      else from_literal_under_impl_82 (pub_u128 0sz)
  }

type t_Q = | Q : t_QCanvas -> t_Q

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

let impl: Core.Convert.t_From t_Q t_QCanvas =
  {
    from
    =
    fun (x: t_QCanvas) ->
      Q
      (rem_under_impl_93 x
          (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QCanvas))
  }

let impl: Core.Convert.t_Into t_Q t_QCanvas =
  { into = fun (self: t_Q) -> self.Hacspec_ovn.Schnorr.Q.0 }

let from_canvas_under_impl_130 (x: t_QCanvas) : t_Q =
  Q
  (rem_under_impl_93 x
      (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_QCanvas))

let into_canvas_under_impl_130 (self: t_Q) : t_QCanvas = self.Hacspec_ovn.Schnorr.Q.0

let max_under_impl_130: t_QCanvas =
  from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

let declassify_under_impl_130 (self: t_Q) : Num_bigint.Bigint.t_BigInt =
  let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into a

let from_hex_under_impl_130 (s: string) : t_Q =
  Core.Convert.Into.into (from_hex_under_impl_81 s <: t_QCanvas)

let from_be_bytes_under_impl_130 (v: slice u8) : t_Q =
  Core.Convert.Into.into (from_be_bytes_under_impl_81 v <: t_QCanvas)

let to_be_bytes_under_impl_130 (self: t_Q) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_be_bytes_under_impl_81 (Core.Convert.Into.into
                self
              <:
              t_QCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let from_le_bytes_under_impl_130 (v: slice u8) : t_Q =
  Core.Convert.Into.into (from_le_bytes_under_impl_81 v <: t_QCanvas)

let to_le_bytes_under_impl_130 (self: t_Q) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (to_le_bytes_under_impl_81 (Core.Convert.Into.into
                self
              <:
              t_QCanvas)
          <:
          array u8 48sz)
      <:
      slice u8)

let bit_under_impl_130 (self: t_Q) (i: usize) : bool =
  bit_under_impl_82 (Core.Convert.Into.into self <: t_QCanvas) i

let from_literal_under_impl_130 (x: u128) : t_Q =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from x in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_130 <: t_QCanvas) <: Num_bigint.Biguint.t_BigUint)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type Q"] in
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
  Q (Core.Convert.Into.into big_x)

let from_signed_literal_under_impl_130 (x: i128) : t_Q =
  let big_x:Num_bigint.Biguint.t_BigUint = Core.Convert.From.from (cast x) in
  let _:Prims.unit =
    if
      big_x >.
      (Core.Convert.Into.into (max_under_impl_130 <: t_QCanvas) <: Num_bigint.Biguint.t_BigUint)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                      (let l = ["literal "; " too big for type Q"] in
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
  Q (Core.Convert.Into.into big_x)

let comp_eq_under_impl_130 (self rhs: t_Q) : t_Q =
  let (x: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_eq_under_impl_81 x (Core.Convert.Into.into rhs <: t_QCanvas)
      <:
      t_QCanvas)

let comp_ne_under_impl_130 (self rhs: t_Q) : t_Q =
  let (x: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_ne_under_impl_81 x (Core.Convert.Into.into rhs <: t_QCanvas)
      <:
      t_QCanvas)

let comp_gte_under_impl_130 (self rhs: t_Q) : t_Q =
  let (x: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gte_under_impl_81 x (Core.Convert.Into.into rhs <: t_QCanvas)
      <:
      t_QCanvas)

let comp_gt_under_impl_130 (self rhs: t_Q) : t_Q =
  let (x: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_gt_under_impl_81 x (Core.Convert.Into.into rhs <: t_QCanvas)
      <:
      t_QCanvas)

let comp_lte_under_impl_130 (self rhs: t_Q) : t_Q =
  let (x: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lte_under_impl_81 x (Core.Convert.Into.into rhs <: t_QCanvas)
      <:
      t_QCanvas)

let comp_lt_under_impl_130 (self rhs: t_Q) : t_Q =
  let (x: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (comp_lt_under_impl_81 x (Core.Convert.Into.into rhs <: t_QCanvas)
      <:
      t_QCanvas)

let neg_under_impl_130 (self: t_Q) : t_Q =
  let (mod_val: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt =
    Core.Convert.Into.into (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

        <:
        t_QCanvas)
  in
  let (s: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  let (s: Num_bigint.Bigint.t_BigInt):Num_bigint.Bigint.t_BigInt = Core.Convert.Into.into s in
  let (result: t_QCanvas):t_QCanvas =
    Core.Convert.Into.into (mod_val -. s <: Core.Ops.Arith.Sub.t_Output)
  in
  Core.Convert.Into.into result

let impl: Core.Cmp.t_PartialOrd t_Q t_Q =
  {
    partial_cmp
    =
    fun (self: t_Q) (other: t_Q) -> Core.Option.Option_Some (Core.Cmp.Ord.cmp self other)
  }

let impl: Core.Cmp.t_Ord t_Q =
  {
    cmp
    =
    fun (self: t_Q) (other: t_Q) ->
      Core.Cmp.Ord.cmp self.Hacspec_ovn.Schnorr.Q.0 other.Hacspec_ovn.Schnorr.Q.0
  }

let impl: Core.Cmp.t_PartialEq t_Q t_Q =
  {
    eq
    =
    fun (self: t_Q) (other: t_Q) -> self.Hacspec_ovn.Schnorr.Q.0 =. other.Hacspec_ovn.Schnorr.Q.0
  }

let impl: Core.Cmp.t_Eq t_Q = {  }

let impl: Core.Ops.Arith.t_Add t_Q t_Q =
  {
    output = t_Q;
    add
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Add.t_Output = a +. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QCanvas):t_QCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Sub t_Q t_Q =
  {
    output = t_Q;
    sub
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QCanvas)
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
      let (d: t_QCanvas):t_QCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Mul t_Q t_Q =
  {
    output = t_Q;
    mul
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Mul.t_Output = a *. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QCanvas):t_QCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Arith.t_Div t_Q t_Q =
  { output = t_Q; div = fun (self: t_Q) (rhs: t_Q) -> self *. (inv_under_impl_124 rhs <: t_Q) }

let impl: Core.Ops.Arith.t_Rem t_Q t_Q =
  {
    output = t_Q;
    rem
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      let (a: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into a
      in
      let (b: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into b
      in
      let (c: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = a %. b in
      let (max: Num_bigint.Biguint.t_BigUint):Num_bigint.Biguint.t_BigUint =
        Core.Convert.Into.into (from_hex_under_impl_81 "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"

            <:
            t_QCanvas)
      in
      let (d: Num_bigint.Biguint.t_BigUint):Core.Ops.Arith.Rem.t_Output = c %. max in
      let (d: t_QCanvas):t_QCanvas = Core.Convert.Into.into d in
      Core.Convert.Into.into d
  }

let impl: Core.Ops.Bit.t_Not t_Q =
  {
    output = t_Q;
    not
    =
    fun (self: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (~.a <: Core.Ops.Bit.Not.t_Output)
  }

let impl: Core.Ops.Bit.t_BitOr t_Q t_Q =
  {
    output = t_Q;
    bitor
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a |. b <: Core.Ops.Bit.BitOr.t_Output)
  }

let impl: Core.Ops.Bit.t_BitXor t_Q t_Q =
  {
    output = t_Q;
    bitxor
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a ^. b <: Core.Ops.Bit.BitXor.t_Output)
  }

let impl: Core.Ops.Bit.t_BitAnd t_Q t_Q =
  {
    output = t_Q;
    bitand
    =
    fun (self: t_Q) (rhs: t_Q) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      let (b: t_QCanvas):t_QCanvas = Core.Convert.Into.into rhs in
      Core.Convert.Into.into (a &. b <: Core.Ops.Bit.BitAnd.t_Output)
  }

let impl: Core.Ops.Bit.t_Shr t_Q usize =
  {
    output = t_Q;
    shr
    =
    fun (self: t_Q) (rhs: usize) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a <<. rhs <: Core.Ops.Bit.Shr.t_Output)
  }

let impl: Core.Ops.Bit.t_Shl t_Q usize =
  {
    output = t_Q;
    shl
    =
    fun (self: t_Q) (rhs: usize) ->
      let (a: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
      Core.Convert.Into.into (a >>. rhs <: Core.Ops.Bit.Shl.t_Output)
  }

let inv_under_impl_124 (self: t_Q) : t_Q =
  let (base: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (inv_under_impl_93 base (max_under_impl_130 <: t_QCanvas) <: t_QCanvas)

let pow_felem_under_impl_124 (self exp: t_Q) : t_Q =
  let (base: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_felem_under_impl_93 base
        (Core.Convert.Into.into exp <: t_QCanvas)
        (max_under_impl_130 <: t_QCanvas)
      <:
      t_QCanvas)

let pow_under_impl_124 (self: t_Q) (exp: u128) : t_Q =
  let (base: t_QCanvas):t_QCanvas = Core.Convert.Into.into self in
  Core.Convert.Into.into (pow_under_impl_93 base exp (max_under_impl_130 <: t_QCanvas) <: t_QCanvas)

let pow2_under_impl_124 (x: usize) : t_Q =
  Core.Convert.Into.into (pow2_under_impl_82 x <: t_QCanvas)

let from_byte_seq_be_under_impl_67 (s: a) : t_Q =
  Core.Convert.Into.into (from_be_bytes_under_impl_81 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_QCanvas)

let from_public_byte_seq_be_under_impl_67 (s: a) : t_Q =
  Core.Convert.Into.into (from_be_bytes_under_impl_81 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_QCanvas)

let to_byte_seq_be_under_impl_67 (self: t_Q) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_be_bytes_under_impl_130 self
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

let to_public_byte_seq_be_under_impl_67 (self: t_Q) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_be_bytes_under_impl_130 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_byte_seq_le_under_impl_67 (s: a) : t_Q =
  Core.Convert.Into.into (from_le_bytes_under_impl_81 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_QCanvas)

let from_public_byte_seq_le_under_impl_67 (s: a) : t_Q =
  Core.Convert.Into.into (from_le_bytes_under_impl_81 (Alloc.Vec.as_slice_under_impl_1 (Core.Iter.Traits.Iterator.Iterator.collect
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
      t_QCanvas)

let to_byte_seq_le_under_impl_67 (self: t_Q) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map
            (Core.Slice.iter_under_impl (Core.Ops.Deref.Deref.deref (to_le_bytes_under_impl_130 self
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

let to_public_byte_seq_le_under_impl_67 (self: t_Q) : Hacspec_lib.Seq.t_Seq u8 =
  Hacspec_lib.Seq.from_vec_under_impl_52 (to_le_bytes_under_impl_130 self
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let from_secret_literal_under_impl_67 (x: Secret_integers.t_U128) : t_Q =
  Core.Convert.Into.into (from_literal_under_impl_82 (Secret_integers.declassify_under_impl_126 x
          <:
          u128)
      <:
      t_QCanvas)

let impl: Hacspec_lib.Traits.t_NumericCopy t_Q = {  }

let impl: Hacspec_lib.Traits.t_UnsignedInteger t_Q = {  }

let impl: Hacspec_lib.Traits.t_UnsignedIntegerCopy t_Q = {  }

let impl: Hacspec_lib.Traits.t_Integer t_Q =
  {
    nUM_BITS = (fun  -> 384sz);
    zERO = (fun  -> from_literal_under_impl_130 (pub_u128 0sz));
    oNE = (fun  -> from_literal_under_impl_130 (pub_u128 1sz));
    tWO = (fun  -> from_literal_under_impl_130 (pub_u128 2sz));
    from_literal = (fun (v_val: u128) -> from_literal_under_impl_130 v_val);
    from_hex_string
    =
    (fun (s: Alloc.String.t_String) ->
        from_hex_under_impl_130 (Core.Ops.Deref.Deref.deref (Alloc.Str.replace_under_impl_5 (Core.Ops.Deref.Deref.deref
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
    (fun (self: t_Q) (i: usize) ->
        (self <<. i <: Core.Ops.Bit.Shr.t_Output) &. (Hacspec_lib.Traits.Integer.v_ONE <: t_Q));
    set_bit
    =
    (fun (self: t_Q) (b: t_Q) (i: usize) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if
                ~.(Prims.op_BarBar (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b
                          <:
                          t_Q)
                        (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
                      <:
                      bool)
                    (Hacspec_lib.Traits.Numeric.equal (Core.Clone.Clone.clone b <: t_Q)
                        (Hacspec_lib.Traits.Integer.v_ZERO <: t_Q)
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
        let tmp1:t_Q = from_literal_under_impl_130 (~.(pub_u128 1sz >>. i <: u128) <: u128) in
        let tmp2:Core.Ops.Bit.Shl.t_Output = b >>. i in
        (self &. tmp1 <: Core.Ops.Bit.BitAnd.t_Output) |. tmp2);
    set
    =
    (fun (self: t_Q) (pos: usize) (y: t_Q) (yi: usize) ->
        let b:t_Q = Hacspec_lib.Traits.Integer.get_bit y yi in
        Hacspec_lib.Traits.Integer.set_bit self b pos);
    rotate_left
    =
    (fun (self: t_Q) (n: usize) ->
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
        ((Core.Clone.Clone.clone self <: t_Q) >>. n <: Core.Ops.Bit.Shl.t_Output) |.
        (self <<.
          (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
            (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
            <:
            usize)
          <:
          Core.Ops.Bit.Shr.t_Output));
    rotate_right
    =
    fun (self: t_Q) (n: usize) ->
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
      ((Core.Clone.Clone.clone self <: t_Q) <<. n <: Core.Ops.Bit.Shr.t_Output) |.
      (self >>.
        (cast (Core.Ops.Arith.Neg.neg (cast n) <: i32) &.
          (Hacspec_lib.Traits.Integer.v_NUM_BITS -. 1sz <: usize)
          <:
          usize)
        <:
        Core.Ops.Bit.Shl.t_Output)
  }

let impl: Hacspec_lib.Traits.t_ModNumeric t_Q =
  {
    sub_mod = (fun (self: t_Q) (rhs: t_Q) (n: t_Q) -> self -. rhs);
    add_mod = (fun (self: t_Q) (rhs: t_Q) (n: t_Q) -> self +. rhs);
    mul_mod = (fun (self: t_Q) (rhs: t_Q) (n: t_Q) -> self *. rhs);
    pow_mod = (fun (self: t_Q) (exp: t_Q) (n: t_Q) -> pow_felem_under_impl_124 self exp);
    modulo = (fun (self: t_Q) (n: t_Q) -> self %. n);
    signed_modulo = (fun (self: t_Q) (n: t_Q) -> Hacspec_lib.Traits.ModNumeric.modulo self n);
    absolute = fun (self: t_Q) -> self
  }

let impl: Hacspec_lib.Traits.t_Numeric t_Q =
  {
    max_val
    =
    (fun  ->
        Core.Convert.Into.into ((max_under_impl_130 <: t_QCanvas) -.
            (from_literal_under_impl_82 (pub_u128 1sz) <: t_QCanvas)
            <:
            Core.Ops.Arith.Sub.t_Output));
    wrap_add = (fun (self: t_Q) (rhs: t_Q) -> self +. rhs);
    wrap_sub = (fun (self: t_Q) (rhs: t_Q) -> self -. rhs);
    wrap_mul = (fun (self: t_Q) (rhs: t_Q) -> self *. rhs);
    wrap_div = (fun (self: t_Q) (rhs: t_Q) -> self /. rhs);
    exp
    =
    (fun (self: t_Q) (exp: u32) -> pow_under_impl_124 self (Core.Convert.Into.into exp <: u128));
    pow_self = (fun (self: t_Q) (exp: t_Q) -> pow_felem_under_impl_124 self exp);
    divide = (fun (self: t_Q) (rhs: t_Q) -> self /. rhs);
    inv = (fun (self: t_Q) (n: t_Q) -> inv_under_impl_124 self);
    equal = (fun (self: t_Q) (other: t_Q) -> self =. other);
    greater_than = (fun (self: t_Q) (other: t_Q) -> self >. other);
    greater_than_or_equal = (fun (self: t_Q) (other: t_Q) -> self >=. other);
    less_than = (fun (self: t_Q) (other: t_Q) -> self <. other);
    less_than_or_equal = (fun (self: t_Q) (other: t_Q) -> self <=. other);
    not_equal_bm
    =
    (fun (self: t_Q) (other: t_Q) ->
        if self <>. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Q) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    equal_bm
    =
    (fun (self: t_Q) (other: t_Q) ->
        if self =. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Q) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_bm
    =
    (fun (self: t_Q) (other: t_Q) ->
        if self >. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Q) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    greater_than_or_equal_bm
    =
    (fun (self: t_Q) (other: t_Q) ->
        if self >=. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Q) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_bm
    =
    (fun (self: t_Q) (other: t_Q) ->
        if self <. other
        then
          ((Hacspec_lib.Traits.Integer.v_ONE <: t_Q) >>. (384sz -. 1sz <: usize)
            <:
            Core.Ops.Bit.Shl.t_Output) -.
          (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
        else Hacspec_lib.Traits.Integer.v_ZERO);
    less_than_or_equal_bm
    =
    fun (self: t_Q) (other: t_Q) ->
      if self <=. other
      then
        ((Hacspec_lib.Traits.Integer.v_ONE <: t_Q) >>. (384sz -. 1sz <: usize)
          <:
          Core.Ops.Bit.Shl.t_Output) -.
        (Hacspec_lib.Traits.Integer.v_ONE <: t_Q)
      else Hacspec_lib.Traits.Integer.v_ZERO
  }

let t_Witness = t_Q

let t_Statement = t_G

let t_Message = t_G

let t_Challenge = t_Q

let t_Response = t_G

let t_Transcript = (t_G & t_G & t_Q & t_G)

let prod_assoc (statement, message: (t_G & t_G)) : Hacspec_ovn.Schnorr.Random_oracle.t_Query =
  Hacspec_lib.Traits.Integer.v_ONE

let verify (h a: t_G) (e: t_Q) (z: t_G) : bool = false

let fiat_shamir_verify (t: (t_G & t_G & t_Q & t_G)) : bool =
  let v_QUERIES:Std.Collections.Hash.Map.t_HashMap Hacspec_ovn.Schnorr.Random_oracle.t_Query
    Hacspec_ovn.Schnorr.Random_oracle.t_Random
    Std.Collections.Hash.Map.t_RandomState =
    Std.Collections.Hash.Map.new_under_impl
  in
  let h, a, e, z:(t_G & t_G & t_Q & t_G) = t in
  let v_QUERIES, eu:(Std.Collections.Hash.Map.t_HashMap Hacspec_ovn.Schnorr.Random_oracle.t_Query
      Hacspec_ovn.Schnorr.Random_oracle.t_Random
      Std.Collections.Hash.Map.t_RandomState &
    Hacspec_ovn.Schnorr.Random_oracle.t_Random) =
    Hacspec_ovn.Schnorr.Random_oracle.random_oracle_query v_QUERIES
      (prod_assoc (h, a) <: Hacspec_ovn.Schnorr.Random_oracle.t_Query)
  in
  verify h a e z

let t_Relation = (t_G & t_Q)

let v_Commit (h: t_G) (w: t_Q) : t_G =
  let r:Hacspec_ovn.Schnorr.Random_oracle.t_Random =
    Hacspec_ovn.Schnorr.Random_oracle.sample_uniform
  in
  let commit:Hacspec_ovn.Schnorr.Random_oracle.t_Random = r in
  Hacspec_lib.Traits.Integer.v_ONE

let v_Response: Rust_primitives.Hax.t_Never =
  Rust_primitives.Hax.failure "AST import:Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: [import_thir:literal] got an error literal: this means the Rust compiler or Hax's frontend probably reported errors above.\n"
    "{ Types.attributes = [];\n  contents =\n  Types.Literal {\n    lit =\n    { Types.node = Types.Err;\n      span =\n      { Types.filename = (Types.Real (Types.LocalPath \"ovn/src/ovn.rs\"));\n        hi = { Types.col = 0; line = 1 }; lo = { Types.col = 0; line = 1 } }\n      };\n    neg = false};\n  hir_id = None;\n  span =\n  { Types.filename = (Types.Real (Types.LocalPath \"ovn/src/schnorr.rs\"));\n    hi = { Types.col = 80; line = 102 }; lo = { Types.col = 0; line = 102 } };\n  ty = Types.Never }"

let fiat_shamir_run: Rust_primitives.Hax.t_Never =
  Rust_primitives.Hax.failure "AST import:Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: [import_thir:literal] got an error literal: this means the Rust compiler or Hax's frontend probably reported errors above.\n"
    "{ Types.attributes = [];\n  contents =\n  Types.Literal {\n    lit =\n    { Types.node = Types.Err;\n      span =\n      { Types.filename = (Types.Real (Types.LocalPath \"ovn/src/ovn.rs\"));\n        hi = { Types.col = 0; line = 1 }; lo = { Types.col = 0; line = 1 } }\n      };\n    neg = false};\n  hir_id = None;\n  span =\n  { Types.filename = (Types.Real (Types.LocalPath \"ovn/src/schnorr.rs\"));\n    hi = { Types.col = 47; line = 108 }; lo = { Types.col = 0; line = 108 } };\n  ty = Types.Never }"