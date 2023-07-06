module Chacha20.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let to_le_u32s_3_ (bytes: slice u8) : t_Array u32 3sz =
  let _:Prims.unit =
    match 3sz, (Core.Slice.len_under_impl bytes <: usize) /. 4sz with
    | left_val, right_val ->
      if ~.(left_val =. right_val <: bool)
      then
        let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
        let ():Prims.unit =
          Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                left_val
                right_val
                Core.Option.Option_None
              <:
              Rust_primitives.Hax.t_Never)
        in
        ()
  in
  let out:t_Array u32 3sz = Rust_primitives.Hax.repeat 0ul 3sz in
  let out:t_Array u32 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 3sz
            })
        <:
        _)
      out
      (fun out i ->
          (out.[ i ] <-
              Core.Num.from_le_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
                        (bytes.[ {
                              Core.Ops.Range.Range.f_start = 4sz *. i <: usize;
                              Core.Ops.Range.Range.f_end = (4sz *. i <: usize) +. 4sz <: usize
                            } ]
                          <:
                          slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 4sz) _)
                  <:
                  t_Array u8 4sz)
              <:
              u32)
          <:
          t_Array u32 3sz)
  in
  out

let to_le_u32s_8_ (bytes: slice u8) : t_Array u32 8sz =
  let _:Prims.unit =
    match 8sz, (Core.Slice.len_under_impl bytes <: usize) /. 4sz with
    | left_val, right_val ->
      if ~.(left_val =. right_val <: bool)
      then
        let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
        let ():Prims.unit =
          Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                left_val
                right_val
                Core.Option.Option_None
              <:
              Rust_primitives.Hax.t_Never)
        in
        ()
  in
  let out:t_Array u32 8sz = Rust_primitives.Hax.repeat 0ul 8sz in
  let out:t_Array u32 8sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 8sz
            })
        <:
        _)
      out
      (fun out i ->
          (out.[ i ] <-
              Core.Num.from_le_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
                        (bytes.[ {
                              Core.Ops.Range.Range.f_start = 4sz *. i <: usize;
                              Core.Ops.Range.Range.f_end = (4sz *. i <: usize) +. 4sz <: usize
                            } ]
                          <:
                          slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 4sz) _)
                  <:
                  t_Array u8 4sz)
              <:
              u32)
          <:
          t_Array u32 8sz)
  in
  out

let to_le_u32s_16_ (bytes: slice u8) : t_Array u32 16sz =
  let _:Prims.unit =
    match 16sz, (Core.Slice.len_under_impl bytes <: usize) /. 4sz with
    | left_val, right_val ->
      if ~.(left_val =. right_val <: bool)
      then
        let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
        let ():Prims.unit =
          Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                left_val
                right_val
                Core.Option.Option_None
              <:
              Rust_primitives.Hax.t_Never)
        in
        ()
  in
  let out:t_Array u32 16sz = Rust_primitives.Hax.repeat 0ul 16sz in
  let out:t_Array u32 16sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 16sz
            })
        <:
        _)
      out
      (fun out i ->
          (out.[ i ] <-
              Core.Num.from_le_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
                        (bytes.[ {
                              Core.Ops.Range.Range.f_start = 4sz *. i <: usize;
                              Core.Ops.Range.Range.f_end = (4sz *. i <: usize) +. 4sz <: usize
                            } ]
                          <:
                          slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 4sz) _)
                  <:
                  t_Array u8 4sz)
              <:
              u32)
          <:
          t_Array u32 16sz)
  in
  out

let u32s_to_le_bytes (state: t_Array u32 16sz) : t_Array u8 64sz =
  let out:t_Array u8 64sz = Rust_primitives.Hax.repeat 0uy 64sz in
  let out:t_Array u8 64sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end
              =
              Core.Slice.len_under_impl (Rust_primitives.unsize state <: slice u32) <: usize
            })
        <:
        _)
      out
      (fun out i ->
          let tmp:t_Array u8 4sz = Core.Num.to_le_bytes_under_impl_8 (state.[ i ] <: u32) in
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = 4sz
                  })
              <:
              _)
            out
            (fun out j ->
                (out.[ (i *. 4sz <: usize) +. j <: usize ] <- tmp.[ j ] <: u8) <: t_Array u8 64sz))
  in
  out

let xor_state (state other: t_Array u32 16sz) : t_Array u32 16sz =
  let state:t_Array u32 16sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 16sz
            })
        <:
        _)
      state
      (fun state i ->
          (state.[ i ] <- (state.[ i ] <: u32) ^. (other.[ i ] <: u32) <: u32) <: t_Array u32 16sz)
  in
  state

let add_state (state other: t_Array u32 16sz) : t_Array u32 16sz =
  let state:t_Array u32 16sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 16sz
            })
        <:
        _)
      state
      (fun state i ->
          (state.[ i ] <-
              Core.Num.wrapping_add_under_impl_8 (state.[ i ] <: u32) (other.[ i ] <: u32) <: u32)
          <:
          t_Array u32 16sz)
  in
  state

let update_array (array: t_Array u8 64sz) (v_val: slice u8) : t_Array u8 64sz =
  let _:Prims.unit =
    if ~.(64sz >=. (Core.Slice.len_under_impl v_val <: usize) <: bool)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: 64 >= val.len()"
            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let array:t_Array u8 64sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Core.Slice.len_under_impl v_val <: usize
            })
        <:
        _)
      array
      (fun array i -> (array.[ i ] <- v_val.[ i ] <: u8) <: t_Array u8 64sz)
  in
  array