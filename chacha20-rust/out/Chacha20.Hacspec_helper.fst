module Chacha20.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

let to_le_u32s_3 (bytes: FStar.Seq.seq UInt8.t)
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 3} =
  let _:Prims.l_False =
    match 3, Prims.op_Division (Core.Slice.len bytes) 4 with
    | left_val, right_val ->
      if Prims.l_Not (left_val = right_val)
      then
        let kind:Core.Panicking.assertKind_t = Core.Panicking.Eq in
        Core.Panicking.assert_failed kind left_val right_val Core.Option.None
  in
  let out:Alloc.Boxed.box_t
    (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 3})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0ul 3
  in
  let out:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 3} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({ start = 0; end = 3 }
          ))
      out
      (fun i out ->
          out.[ i ] <-
            Core.Num.from_le_bytes (Core.Result.unwrap (Core.Convert.TryInto.try_into bytes.[ {
                          start = 4 * i;
                          end = 4 * i + 4
                        } ])))
  in
  out

let to_le_u32s_8 (bytes: FStar.Seq.seq UInt8.t)
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
  let _:Prims.l_False =
    match 8, Prims.op_Division (Core.Slice.len bytes) 4 with
    | left_val, right_val ->
      if Prims.l_Not (left_val = right_val)
      then
        let kind:Core.Panicking.assertKind_t = Core.Panicking.Eq in
        Core.Panicking.assert_failed kind left_val right_val Core.Option.None
  in
  let out:Alloc.Boxed.box_t
    (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0ul 8
  in
  let out:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({ start = 0; end = 8 }
          ))
      out
      (fun i out ->
          out.[ i ] <-
            Core.Num.from_le_bytes (Core.Result.unwrap (Core.Convert.TryInto.try_into bytes.[ {
                          start = 4 * i;
                          end = 4 * i + 4
                        } ])))
  in
  out

let to_le_u32s_16 (bytes: FStar.Seq.seq UInt8.t)
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let _:Prims.l_False =
    match 16, Prims.op_Division (Core.Slice.len bytes) 4 with
    | left_val, right_val ->
      if Prims.l_Not (left_val = right_val)
      then
        let kind:Core.Panicking.assertKind_t = Core.Panicking.Eq in
        Core.Panicking.assert_failed kind left_val right_val Core.Option.None
  in
  let out:Alloc.Boxed.box_t
    (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0ul 16
  in
  let out:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = 16
            }))
      out
      (fun i out ->
          out.[ i ] <-
            Core.Num.from_le_bytes (Core.Result.unwrap (Core.Convert.TryInto.try_into bytes.[ {
                          start = 4 * i;
                          end = 4 * i + 4
                        } ])))
  in
  out

let u32s_to_le_bytes
      (state: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  let out:Alloc.Boxed.box_t
    (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0uy 64
  in
  let out:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = Core.Slice.len (Hacspec.Lib.unsize state)
            }))
      out
      (fun i out ->
          let tmp:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 4} =
            Core.Num.to_le_bytes (Core.Ops.Index.index state i)
          in
          Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    start = 0;
                    end = 4
                  }))
            out
            (fun j out -> out.[ i * 4 + j ] <- Core.Ops.Index.index tmp j))
  in
  out

let xor_state
      (state other: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = 16
            }))
      state
      (fun i state ->
          state.[ i ] <-
            Hacspec_lib.^. (Core.Ops.Index.index state i) (Core.Ops.Index.index other i))
  in
  state

let add_state
      (state other: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = 16
            }))
      state
      (fun i state ->
          state.[ i ] <-
            Core.Num.wrapping_add (Core.Ops.Index.index state i) (Core.Ops.Index.index other i))
  in
  state

let update_array
      (array: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}))
      (val: FStar.Seq.seq UInt8.t)
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  let _:Prims.l_False =
    if Prims.l_Not (Prims.op_GreaterThan 64 (Core.Slice.len val))
    then Core.Panicking.panic "assertion failed: 64 >= val.len()"
  in
  let array:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = Core.Slice.len val
            }))
      array
      (fun i array -> array.[ i ] <- Core.Ops.Index.index val i)
  in
  array