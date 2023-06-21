module Chacha20.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core


// let update_array (array: array u8 64sz) (valx: slice u8) : array u8 64sz = admit ()
let add_state (state other: array u32 16sz) : array u32 16sz = admit ()
let xor_state (state other: array u32 16sz) : array u32 16sz = admit ()
let u32s_to_le_bytes (state: array u32 16sz) : array u8 64sz = admit ()
let to_le_u32s_16_ (bytes: slice u8) : array u32 16sz = admit ()
let to_le_u32s_8_ (bytes: slice u8) : array u32 8sz = admit ()
let to_le_u32s_3_ (bytes: slice u8) : array u32 3sz = admit ()

// let to_le_u32s_3_ (bytes: slice u8) : array u32 3sz =
//   let _:never =
//     match 3sz, Core.Slice.len_under_impl bytes / 4sz with
//     | left_val, right_val ->
//       if ~(left_val =. right_val)
//       then
//         let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
//         Core.Panicking.assert_failed kind left_val right_val Core.Option.Option_None
//   in
//   let out:array u32 3sz = Hax.Array.repeat 0ul 3sz in
//   let out:array u32 3sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = 3sz
//             }))
//       out
//       (fun i out ->
//           out.[ i ] <-
//             Core.Num.from_le_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
//                       bytes.[ { f_start = 4sz * i; f_end = 4sz * i + 4sz } ])))
//   in
//   out

// let to_le_u32s_8_ (bytes: slice u8) : array u32 8sz =
//   let _:never =
//     match 8sz, Core.Slice.len_under_impl bytes / 4sz with
//     | left_val, right_val ->
//       if ~(left_val =. right_val)
//       then
//         let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
//         Core.Panicking.assert_failed kind left_val right_val Core.Option.Option_None
//   in
//   let out:array u32 8sz = Hax.Array.repeat 0ul 8sz in
//   let out:array u32 8sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = 8sz
//             }))
//       out
//       (fun i out ->
//           out.[ i ] <-
//             Core.Num.from_le_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
//                       bytes.[ { f_start = 4sz * i; f_end = 4sz * i + 4sz } ])))
//   in
//   out

// let to_le_u32s_16_ (bytes: slice u8) : array u32 16sz =
//   let _:never =
//     match 16sz, Core.Slice.len_under_impl bytes / 4sz with
//     | left_val, right_val ->
//       if ~(left_val =. right_val)
//       then
//         let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
//         Core.Panicking.assert_failed kind left_val right_val Core.Option.Option_None
//   in
//   let out:array u32 16sz = Hax.Array.repeat 0ul 16sz in
//   let out:array u32 16sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = 16sz
//             }))
//       out
//       (fun i out ->
//           out.[ i ] <-
//             Core.Num.from_le_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
//                       bytes.[ { f_start = 4sz * i; f_end = 4sz * i + 4sz } ])))
//   in
//   out

// let u32s_to_le_bytes (state: array u32 16sz) : array u8 64sz =
//   let out:array u8 64sz = Hax.Array.repeat 0uy 64sz in
//   let out:array u8 64sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = Core.Slice.len_under_impl (Hax.CoerceUnsize.unsize state)
//             }))
//       out
//       (fun i out ->
//           let tmp:array u8 4sz = Core.Num.to_le_bytes_under_impl_8 state.[ i ] in
//           Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//                     f_start = 0sz;
//                     f_end = 4sz
//                   }))
//             out
//             (fun j out -> out.[ i * 4sz + j ] <- tmp.[ j ]))
//   in
//   out

// let xor_state (state other: array u32 16sz) : array u32 16sz =
//   let state:array u32 16sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = 16sz
//             }))
//       state
//       (fun i state -> state.[ i ] <- state.[ i ] ^ other.[ i ])
//   in
//   state

// let add_state (state other: array u32 16sz) : array u32 16sz =
//   let state:array u32 16sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = 16sz
//             }))
//       state
//       (fun i state -> state.[ i ] <- Core.Num.wrapping_add_under_impl_8 state.[ i ] other.[ i ])
//   in
//   state

// let update_array (array: array u8 64sz) (valx: slice u8) : array u8 64sz =
//   let _:never =
//     if ~(64sz >= Core.Slice.len_under_impl valx)
//     then Core.Panicking.panic "assertion failed: 64 >= val.len()"
//   in
//   let array:array u8 64sz =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = Core.Slice.len_under_impl valx
//             }))
//       array
//       (fun i array -> array.[ i ] <- valx.[ i ])
//   in
//   array
