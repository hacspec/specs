module Natmod
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

type natModAttr_t = {
  mod_str:Alloc.String.string_t;
  mod_bytes:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t;
  int_size:uint_size
}

let impl: Syn.Parse.Parse natModAttr_t =
  {
    parse
    =
    fun (input: Syn.Parse.parseBuffer_t) ->
      let hoist1:Core.Result.result_t natModAttr_t Syn.Error.error_t =
        Std.Ops.FromResidual.from_residual (Syn.Parse.parse input)
      in
      let mod_str:Alloc.String.string_t = Syn.Lit.value hoist1 in
      let mod_bytes:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
        Core.Result.expect (Hex.FromHex.from_hex mod_str) "Invalid hex String"
      in
      let _:Core.Result.result_t natModAttr_t Syn.Error.error_t =
        Std.Ops.FromResidual.from_residual (Syn.Parse.parse input)
      in
      let hoist2:Core.Result.result_t natModAttr_t Syn.Error.error_t =
        Std.Ops.FromResidual.from_residual (Syn.Parse.parse input)
      in
      let hoist3:Core.Result.result_t uint_size Syn.Error.error_t = Syn.Lit.base10_parse hoist2 in
      let int_size:Core.Result.result_t natModAttr_t Syn.Error.error_t =
        Std.Ops.FromResidual.from_residual hoist3
      in
      let _:Prims.l_False =
        if Prims.l_Not (Syn.Parse.is_empty input)
        then
          Core.Panicking.panic_fmt (Core.Fmt.new_v1 (Hacspec.Lib.unsize [
                      "Left over tokens in attribute "
                    ])
                (Hacspec.Lib.unsize [Core.Fmt.Rt.new_debug input]))
      in
      Core.Result.Ok ({ mod_str = mod_str; mod_bytes = mod_bytes; int_size = int_size })
  }

let nat_mod (attr item: Proc_macro.tokenStream_t) : Proc_macro.tokenStream_t =
  Hacspec.Lib.run (let* item_ast:Syn.Derive.deriveInput_t =
        match Syn.parse item with
        | Core.Result.Ok data -> Std.Ops.ControlFlow.Continue data
        | Core.Result.Err err ->
          Std.Ops.ControlFlow.break (Core.Convert.From.from (Syn.Error.to_compile_error err))
      in
      let ident:Proc_macro2.ident_t = Core.Clone.Clone.clone item_ast.ident in
      let* args:natModAttr_t =
        match Syn.parse attr with
        | Core.Result.Ok data -> Std.Ops.ControlFlow.Continue data
        | Core.Result.Err err ->
          Std.Ops.ControlFlow.break (Core.Convert.From.from (Syn.Error.to_compile_error err))
      in
      Std.Ops.ControlFlow.Continue
      (let num_bytes:uint_size = args.int_size in
        let modulus:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t = args.mod_bytes in
        let modulus_string:Alloc.String.string_t = args.mod_str in
        let padded_modulus:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
          Alloc.Vec.from_elem 0uy (num_bytes - Alloc.Vec.len modulus)
        in
        let _:Prims.unit =
          Hax_error.hax_failure ""
            "alloc::vec::append(\n        &mut (padded_modulus),\n        &mut (deref(&mut (core::clone::Clone::clone(&(modulus))))),\n    )"

        in
        let mod_iter1:Core.Slice.Iter.iter_t UInt8.t =
          Core.Slice.iter (Core.Ops.Deref.Deref.deref padded_modulus)
        in
        let mod_iter2:Core.Slice.Iter.iter_t UInt8.t =
          Core.Slice.iter (Core.Ops.Deref.Deref.deref padded_modulus)
        in
        let mod_iter3:Core.Slice.Iter.iter_t UInt8.t =
          Core.Slice.iter (Core.Ops.Deref.Deref.deref padded_modulus)
        in
        let res:Alloc.String.string_t =
          Alloc.Fmt.format (Core.Fmt.new_v1 (Hacspec.Lib.unsize [""; "_MODULUS"])
                (Hacspec.Lib.unsize [
                      Core.Fmt.Rt.new_display (Alloc.Str.to_uppercase (Core.Ops.Deref.Deref.deref (Alloc.String.ToString.to_string
                                    ident)))
                    ]))
        in
        let const_name:Proc_macro2.ident_t =
          Proc_macro2.new_ (Core.Ops.Deref.Deref.deref res) (Proc_macro2.span ident)
        in
        let res:Alloc.String.string_t =
          Alloc.Fmt.format (Core.Fmt.new_v1 (Hacspec.Lib.unsize [""; "_MODULUS_STR"])
                (Hacspec.Lib.unsize [
                      Core.Fmt.Rt.new_display (Alloc.Str.to_uppercase (Core.Ops.Deref.Deref.deref (Alloc.String.ToString.to_string
                                    ident)))
                    ]))
        in
        let static_name:Proc_macro2.ident_t =
          Proc_macro2.new_ (Core.Ops.Deref.Deref.deref res) (Proc_macro2.span ident)
        in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist8:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "derive" in
        let hoist5:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Clone" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Copy" in
        let hoist4:Proc_macro2.tokenStream_t = _s in
        let hoist6:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist5 Proc_macro2.Parenthesis hoist4
        in
        let _s:Proc_macro2.tokenStream_t = hoist6 in
        let hoist7:Proc_macro2.tokenStream_t = _s in
        let hoist9:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist8 Proc_macro2.Bracket hoist7
        in
        let _s:Proc_macro2.tokenStream_t = hoist9 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#struct" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist14:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let hoist11:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist10:Proc_macro2.tokenStream_t = _s in
        let hoist12:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist11 Proc_macro2.Bracket hoist10
        in
        let _s:Proc_macro2.tokenStream_t = hoist12 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let hoist13:Proc_macro2.tokenStream_t = _s in
        let hoist15:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist14 Proc_macro2.Brace hoist13
        in
        let _s:Proc_macro2.tokenStream_t = hoist15 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#const" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens const_name _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let hoist17:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist16:Proc_macro2.tokenStream_t = _s in
        let hoist18:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist17 Proc_macro2.Bracket hoist16
        in
        let _s:Proc_macro2.tokenStream_t = hoist18 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let hoist21:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _i:uint_size = 0 in
        let has_iter:Quote.__private.thereIsNoIteratorInRepetition_t = {  } in
        let mod_iter1, i:(Core.Slice.Iter.iter_t UInt8.t & Quote.__private.hasIterator_t) =
          Quote.__private.Ext.RepIteratorExt.quote_into_iter mod_iter1
        in
        let has_iter = has_iter |. i in
        let (_: Quote.__private.hasIterator_t):Quote.__private.hasIterator_t = has_iter in
        let _i, _s, mod_iter1:(Prims.unit & Proc_macro2.tokenStream_t &
          Core.Slice.Iter.iter_t UInt8.t) =
          Hax_error.hax_failure ""
            "{\n        (loop {\n            |Tuple3(_i, _s, mod_iter1)| {\n                (if true {\n                    {\n                        let Tuple2(todo_fresh_var, mod_iter1_temp): tuple2<\n                            core::option::Option<proj_asso_type!()>,\n                            core::slice::iter::Iter<int>,\n                        > = { core::iter::traits::iterator::Iterator::next(mod_iter1) };\n                        {\n                            let mod_iter1: core::slice::iter::Iter<int> = { mod_iter1_temp };\n                            {\n                                let hoist19: core::option::Option<proj_asso_type!()> =\n                                    { todo_fresh_var };\n                                {\n                                    let mod_iter1: quote::__private::RepInterp<int> = {\n                                        (match hoist19 {\n                                            core::option::Some(_x) => {\n                                                quote::__private::RepInterp(_x)\n                                            }\n                                            core::option::None => {\n                                                hax_error::hax_failure(\"\", \"(break (Tuple0))\")\n                                            }\n                                        })\n                                    };\n                                    {\n                                        let _s: proc_macro2::TokenStream = {\n                                            (if BinOp::Ast.Gt(_i, 0) {\n                                                {\n                                                    let _s: proc_macro2::TokenStream =\n                                                        { quote::__private::push_comma(_s) };\n                                                    _s\n                                                }\n                                            } else {\n                                                _s\n                                            })\n                                        };\n                                        {\n                                            let Tuple0: tuple0 = { BinOp::Ast.Add(_i, 1) };\n                                            {\n                                                let _i: tuple0 = { Tuple0 };\n                                                {\n                                                    let _s: proc_macro2::TokenStream = {\n                                                        quote::to_tokens::ToTokens::to_tokens(\n                                                            mod_iter1, _s,\n                                                        )\n                                                    };\n                                                    Tuple3(_i, _s, mod_iter1)\n                                                }\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        }\n                    }\n                } else {\n                    {\n                        let _: tuple0 = { hax_error::hax_failure(\"\", \"(break (Tuple0))\") };\n                        Tuple3(_i, _s, mod_iter1)\n                    }\n                })\n            }\n        })(Tuple3(_i, _s, mod_iter1))\n    }"

        in
        let hoist20:Proc_macro2.tokenStream_t = _s in
        let hoist22:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist21 Proc_macro2.Bracket hoist20
        in
        let _s:Proc_macro2.tokenStream_t = hoist22 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#static" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens static_name _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "str" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens modulus_string _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "NatMod" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_gt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist31:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#const" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "MODULUS" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist28:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let hoist25:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _i:uint_size = 0 in
        let has_iter:Quote.__private.thereIsNoIteratorInRepetition_t = {  } in
        let mod_iter2, i:(Core.Slice.Iter.iter_t UInt8.t & Quote.__private.hasIterator_t) =
          Quote.__private.Ext.RepIteratorExt.quote_into_iter mod_iter2
        in
        let has_iter = has_iter |. i in
        let (_: Quote.__private.hasIterator_t):Quote.__private.hasIterator_t = has_iter in
        let _i, _s, mod_iter2:(Prims.unit & Proc_macro2.tokenStream_t &
          Core.Slice.Iter.iter_t UInt8.t) =
          Hax_error.hax_failure ""
            "{\n        (loop {\n            |Tuple3(_i, _s, mod_iter2)| {\n                (if true {\n                    {\n                        let Tuple2(todo_fresh_var, mod_iter2_temp): tuple2<\n                            core::option::Option<proj_asso_type!()>,\n                            core::slice::iter::Iter<int>,\n                        > = { core::iter::traits::iterator::Iterator::next(mod_iter2) };\n                        {\n                            let mod_iter2: core::slice::iter::Iter<int> = { mod_iter2_temp };\n                            {\n                                let hoist23: core::option::Option<proj_asso_type!()> =\n                                    { todo_fresh_var };\n                                {\n                                    let mod_iter2: quote::__private::RepInterp<int> = {\n                                        (match hoist23 {\n                                            core::option::Some(_x) => {\n                                                quote::__private::RepInterp(_x)\n                                            }\n                                            core::option::None => {\n                                                hax_error::hax_failure(\"\", \"(break (Tuple0))\")\n                                            }\n                                        })\n                                    };\n                                    {\n                                        let _s: proc_macro2::TokenStream = {\n                                            (if BinOp::Ast.Gt(_i, 0) {\n                                                {\n                                                    let _s: proc_macro2::TokenStream =\n                                                        { quote::__private::push_comma(_s) };\n                                                    _s\n                                                }\n                                            } else {\n                                                _s\n                                            })\n                                        };\n                                        {\n                                            let Tuple0: tuple0 = { BinOp::Ast.Add(_i, 1) };\n                                            {\n                                                let _i: tuple0 = { Tuple0 };\n                                                {\n                                                    let _s: proc_macro2::TokenStream = {\n                                                        quote::to_tokens::ToTokens::to_tokens(\n                                                            mod_iter2, _s,\n                                                        )\n                                                    };\n                                                    Tuple3(_i, _s, mod_iter2)\n                                                }\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        }\n                    }\n                } else {\n                    {\n                        let _: tuple0 = { hax_error::hax_failure(\"\", \"(break (Tuple0))\") };\n                        Tuple3(_i, _s, mod_iter2)\n                    }\n                })\n            }\n        })(Tuple3(_i, _s, mod_iter2))\n    }"

        in
        let hoist24:Proc_macro2.tokenStream_t = _s in
        let hoist26:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist25 Proc_macro2.Bracket hoist24
        in
        let _s:Proc_macro2.tokenStream_t = hoist26 in
        let hoist27:Proc_macro2.tokenStream_t = _s in
        let hoist29:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist28 Proc_macro2.Brace hoist27
        in
        let _s:Proc_macro2.tokenStream_t = hoist29 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#const" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "MODULUS_STR" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lifetime _s "'static" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "str" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens modulus_string _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let hoist30:Proc_macro2.tokenStream_t = _s in
        let hoist32:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist31 Proc_macro2.Brace hoist30
        in
        let _s:Proc_macro2.tokenStream_t = hoist32 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist197:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist34:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Get the modulus as string\""
        in
        let hoist33:Proc_macro2.tokenStream_t = _s in
        let hoist35:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist34 Proc_macro2.Bracket hoist33
        in
        let _s:Proc_macro2.tokenStream_t = hoist35 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#const" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus_string" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lifetime _s "'static" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "str" in
        let hoist37:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens modulus_string _s in
        let hoist36:Proc_macro2.tokenStream_t = _s in
        let hoist38:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist37 Proc_macro2.Brace hoist36
        in
        let _s:Proc_macro2.tokenStream_t = hoist38 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist40:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Get the modulus as byte array\""
        in
        let hoist39:Proc_macro2.tokenStream_t = _s in
        let hoist41:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist40 Proc_macro2.Bracket hoist39
        in
        let _s:Proc_macro2.tokenStream_t = hoist41 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#const" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let hoist43:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist42:Proc_macro2.tokenStream_t = _s in
        let hoist44:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist43 Proc_macro2.Bracket hoist42
        in
        let _s:Proc_macro2.tokenStream_t = hoist44 in
        let hoist50:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let hoist47:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _i:uint_size = 0 in
        let has_iter:Quote.__private.thereIsNoIteratorInRepetition_t = {  } in
        let mod_iter3, i:(Core.Slice.Iter.iter_t UInt8.t & Quote.__private.hasIterator_t) =
          Quote.__private.Ext.RepIteratorExt.quote_into_iter mod_iter3
        in
        let has_iter = has_iter |. i in
        let (_: Quote.__private.hasIterator_t):Quote.__private.hasIterator_t = has_iter in
        let _i, _s, mod_iter3:(Prims.unit & Proc_macro2.tokenStream_t &
          Core.Slice.Iter.iter_t UInt8.t) =
          Hax_error.hax_failure ""
            "{\n        (loop {\n            |Tuple3(_i, _s, mod_iter3)| {\n                (if true {\n                    {\n                        let Tuple2(todo_fresh_var, mod_iter3_temp): tuple2<\n                            core::option::Option<proj_asso_type!()>,\n                            core::slice::iter::Iter<int>,\n                        > = { core::iter::traits::iterator::Iterator::next(mod_iter3) };\n                        {\n                            let mod_iter3: core::slice::iter::Iter<int> = { mod_iter3_temp };\n                            {\n                                let hoist45: core::option::Option<proj_asso_type!()> =\n                                    { todo_fresh_var };\n                                {\n                                    let mod_iter3: quote::__private::RepInterp<int> = {\n                                        (match hoist45 {\n                                            core::option::Some(_x) => {\n                                                quote::__private::RepInterp(_x)\n                                            }\n                                            core::option::None => {\n                                                hax_error::hax_failure(\"\", \"(break (Tuple0))\")\n                                            }\n                                        })\n                                    };\n                                    {\n                                        let _s: proc_macro2::TokenStream = {\n                                            (if BinOp::Ast.Gt(_i, 0) {\n                                                {\n                                                    let _s: proc_macro2::TokenStream =\n                                                        { quote::__private::push_comma(_s) };\n                                                    _s\n                                                }\n                                            } else {\n                                                _s\n                                            })\n                                        };\n                                        {\n                                            let Tuple0: tuple0 = { BinOp::Ast.Add(_i, 1) };\n                                            {\n                                                let _i: tuple0 = { Tuple0 };\n                                                {\n                                                    let _s: proc_macro2::TokenStream = {\n                                                        quote::to_tokens::ToTokens::to_tokens(\n                                                            mod_iter3, _s,\n                                                        )\n                                                    };\n                                                    Tuple3(_i, _s, mod_iter3)\n                                                }\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        }\n                    }\n                } else {\n                    {\n                        let _: tuple0 = { hax_error::hax_failure(\"\", \"(break (Tuple0))\") };\n                        Tuple3(_i, _s, mod_iter3)\n                    }\n                })\n            }\n        })(Tuple3(_i, _s, mod_iter3))\n    }"

        in
        let hoist46:Proc_macro2.tokenStream_t = _s in
        let hoist48:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist47 Proc_macro2.Bracket hoist46
        in
        let _s:Proc_macro2.tokenStream_t = hoist48 in
        let hoist49:Proc_macro2.tokenStream_t = _s in
        let hoist51:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist50 Proc_macro2.Brace hoist49
        in
        let _s:Proc_macro2.tokenStream_t = hoist51 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist53:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "r\" New from hex string\"" in
        let hoist52:Proc_macro2.tokenStream_t = _s in
        let hoist54:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist53 Proc_macro2.Bracket hoist52
        in
        let _s:Proc_macro2.tokenStream_t = hoist54 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_hex" in
        let hoist56:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "hex" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "str" in
        let hoist55:Proc_macro2.tokenStream_t = _s in
        let hoist57:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist56 Proc_macro2.Parenthesis hoist55
        in
        let _s:Proc_macro2.tokenStream_t = hoist57 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist86:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "assert" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist59:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "hex" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rem _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "2" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0" in
        let hoist58:Proc_macro2.tokenStream_t = _s in
        let hoist60:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist59 Proc_macro2.Parenthesis hoist58
        in
        let _s:Proc_macro2.tokenStream_t = hoist60 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "l" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "hex" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_div _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "2" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "assert" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist62:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "l" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_le _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist61:Proc_macro2.tokenStream_t = _s in
        let hoist63:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist62 Proc_macro2.Parenthesis hoist61
        in
        let _s:Proc_macro2.tokenStream_t = hoist63 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#mut" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let hoist65:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist64:Proc_macro2.tokenStream_t = _s in
        let hoist66:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist65 Proc_macro2.Bracket hoist64
        in
        let _s:Proc_macro2.tokenStream_t = hoist66 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "skip" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_sub _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "l" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#in" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "l" in
        let hoist80:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist68:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "skip" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_add _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let hoist67:Proc_macro2.tokenStream_t = _s in
        let hoist69:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist68 Proc_macro2.Bracket hoist67
        in
        let _s:Proc_macro2.tokenStream_t = hoist69 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_str_radix" in
        let hoist74:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "hex" in
        let hoist71:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "2" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_star _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "2" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_star _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_add _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "2" in
        let hoist70:Proc_macro2.tokenStream_t = _s in
        let hoist72:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist71 Proc_macro2.Bracket hoist70
        in
        let _s:Proc_macro2.tokenStream_t = hoist72 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "16" in
        let hoist73:Proc_macro2.tokenStream_t = _s in
        let hoist75:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist74 Proc_macro2.Parenthesis hoist73
        in
        let _s:Proc_macro2.tokenStream_t = hoist75 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "expect" in
        let hoist77:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "\"An unexpected error occurred.\""
        in
        let hoist76:Proc_macro2.tokenStream_t = _s in
        let hoist78:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist77 Proc_macro2.Parenthesis hoist76
        in
        let _s:Proc_macro2.tokenStream_t = hoist78 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let hoist79:Proc_macro2.tokenStream_t = _s in
        let hoist81:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist80 Proc_macro2.Brace hoist79
        in
        let _s:Proc_macro2.tokenStream_t = hoist81 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist83:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist82:Proc_macro2.tokenStream_t = _s in
        let hoist84:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist83 Proc_macro2.Brace hoist82
        in
        let _s:Proc_macro2.tokenStream_t = hoist84 in
        let hoist85:Proc_macro2.tokenStream_t = _s in
        let hoist87:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist86 Proc_macro2.Brace hoist85
        in
        let _s:Proc_macro2.tokenStream_t = hoist87 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist89:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Get hex string representation of this.\""
        in
        let hoist88:Proc_macro2.tokenStream_t = _s in
        let hoist90:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist89 Proc_macro2.Bracket hoist88
        in
        let _s:Proc_macro2.tokenStream_t = hoist90 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_hex" in
        let hoist92:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let hoist91:Proc_macro2.tokenStream_t = _s in
        let hoist93:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist92 Proc_macro2.Parenthesis hoist91
        in
        let _s:Proc_macro2.tokenStream_t = hoist93 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "String" in
        let hoist104:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "strs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Vec" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "String" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_gt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "iter" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "map" in
        let hoist98:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_or _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "b" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_or _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "format" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist95:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "\"{:02x}\"" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "b" in
        let hoist94:Proc_macro2.tokenStream_t = _s in
        let hoist96:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist95 Proc_macro2.Parenthesis hoist94
        in
        let _s:Proc_macro2.tokenStream_t = hoist96 in
        let hoist97:Proc_macro2.tokenStream_t = _s in
        let hoist99:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist98 Proc_macro2.Parenthesis hoist97
        in
        let _s:Proc_macro2.tokenStream_t = hoist99 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "collect" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "strs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "join" in
        let hoist101:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "\"\"" in
        let hoist100:Proc_macro2.tokenStream_t = _s in
        let hoist102:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist101 Proc_macro2.Parenthesis hoist100
        in
        let _s:Proc_macro2.tokenStream_t = hoist102 in
        let hoist103:Proc_macro2.tokenStream_t = _s in
        let hoist105:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist104 Proc_macro2.Brace hoist103
        in
        let _s:Proc_macro2.tokenStream_t = hoist105 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist107:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "r\" Zero element\"" in
        let hoist106:Proc_macro2.tokenStream_t = _s in
        let hoist108:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist107 Proc_macro2.Bracket hoist106
        in
        let _s:Proc_macro2.tokenStream_t = hoist108 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#const" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "zero" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist116:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist113:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let hoist110:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist109:Proc_macro2.tokenStream_t = _s in
        let hoist111:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist110 Proc_macro2.Bracket hoist109
        in
        let _s:Proc_macro2.tokenStream_t = hoist111 in
        let hoist112:Proc_macro2.tokenStream_t = _s in
        let hoist114:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist113 Proc_macro2.Brace hoist112
        in
        let _s:Proc_macro2.tokenStream_t = hoist114 in
        let hoist115:Proc_macro2.tokenStream_t = _s in
        let hoist117:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist116 Proc_macro2.Brace hoist115
        in
        let _s:Proc_macro2.tokenStream_t = hoist117 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist119:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Returns 2 to the power of the argument\""
        in
        let hoist118:Proc_macro2.tokenStream_t = _s in
        let hoist120:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist119 Proc_macro2.Bracket hoist118
        in
        let _s:Proc_macro2.tokenStream_t = hoist120 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "pow2" in
        let hoist122:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "usize" in
        let hoist121:Proc_macro2.tokenStream_t = _s in
        let hoist123:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist122 Proc_macro2.Parenthesis hoist121
        in
        let _s:Proc_macro2.tokenStream_t = hoist123 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist128:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from" in
        let hoist125:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "1u32" in
        let hoist124:Proc_macro2.tokenStream_t = _s in
        let hoist126:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist125 Proc_macro2.Parenthesis hoist124
        in
        let _s:Proc_macro2.tokenStream_t = hoist126 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_shl _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "into" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist127:Proc_macro2.tokenStream_t = _s in
        let hoist129:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist128 Proc_macro2.Brace hoist127
        in
        let _s:Proc_macro2.tokenStream_t = hoist129 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist131:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Create a new [`#ident`] from a `u128` literal.\""
        in
        let hoist130:Proc_macro2.tokenStream_t = _s in
        let hoist132:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist131 Proc_macro2.Bracket hoist130
        in
        let _s:Proc_macro2.tokenStream_t = hoist132 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_u128" in
        let hoist134:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "literal" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u128" in
        let hoist133:Proc_macro2.tokenStream_t = _s in
        let hoist135:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist134 Proc_macro2.Parenthesis hoist133
        in
        let _s:Proc_macro2.tokenStream_t = hoist135 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist143:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from" in
        let hoist140:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from" in
        let hoist137:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "literal" in
        let hoist136:Proc_macro2.tokenStream_t = _s in
        let hoist138:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist137 Proc_macro2.Parenthesis hoist136
        in
        let _s:Proc_macro2.tokenStream_t = hoist138 in
        let hoist139:Proc_macro2.tokenStream_t = _s in
        let hoist141:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist140 Proc_macro2.Parenthesis hoist139
        in
        let _s:Proc_macro2.tokenStream_t = hoist141 in
        let hoist142:Proc_macro2.tokenStream_t = _s in
        let hoist144:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist143 Proc_macro2.Brace hoist142
        in
        let _s:Proc_macro2.tokenStream_t = hoist144 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist146:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Create a new [`#ident`] from a little endian byte slice.\""
        in
        let hoist145:Proc_macro2.tokenStream_t = _s in
        let hoist147:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist146 Proc_macro2.Bracket hoist145
        in
        let _s:Proc_macro2.tokenStream_t = hoist147 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_le_bytes" in
        let hoist152:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let hoist149:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let hoist148:Proc_macro2.tokenStream_t = _s in
        let hoist150:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist149 Proc_macro2.Bracket hoist148
        in
        let _s:Proc_macro2.tokenStream_t = hoist150 in
        let hoist151:Proc_macro2.tokenStream_t = _s in
        let hoist153:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist152 Proc_macro2.Parenthesis hoist151
        in
        let _s:Proc_macro2.tokenStream_t = hoist153 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist161:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from" in
        let hoist158:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_le" in
        let hoist155:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let hoist154:Proc_macro2.tokenStream_t = _s in
        let hoist156:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist155 Proc_macro2.Parenthesis hoist154
        in
        let _s:Proc_macro2.tokenStream_t = hoist156 in
        let hoist157:Proc_macro2.tokenStream_t = _s in
        let hoist159:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist158 Proc_macro2.Parenthesis hoist157
        in
        let _s:Proc_macro2.tokenStream_t = hoist159 in
        let hoist160:Proc_macro2.tokenStream_t = _s in
        let hoist162:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist161 Proc_macro2.Brace hoist160
        in
        let _s:Proc_macro2.tokenStream_t = hoist162 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_pound _s in
        let hoist164:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "doc" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "r\" Create a new [`#ident`] from a little endian byte slice.\""
        in
        let hoist163:Proc_macro2.tokenStream_t = _s in
        let hoist165:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist164 Proc_macro2.Bracket hoist163
        in
        let _s:Proc_macro2.tokenStream_t = hoist165 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_be_bytes" in
        let hoist170:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let hoist167:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let hoist166:Proc_macro2.tokenStream_t = _s in
        let hoist168:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist167 Proc_macro2.Bracket hoist166
        in
        let _s:Proc_macro2.tokenStream_t = hoist168 in
        let hoist169:Proc_macro2.tokenStream_t = _s in
        let hoist171:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist170 Proc_macro2.Parenthesis hoist169
        in
        let _s:Proc_macro2.tokenStream_t = hoist171 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist179:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from" in
        let hoist176:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist173:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let hoist172:Proc_macro2.tokenStream_t = _s in
        let hoist174:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist173 Proc_macro2.Parenthesis hoist172
        in
        let _s:Proc_macro2.tokenStream_t = hoist174 in
        let hoist175:Proc_macro2.tokenStream_t = _s in
        let hoist177:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist176 Proc_macro2.Parenthesis hoist175
        in
        let _s:Proc_macro2.tokenStream_t = hoist177 in
        let hoist178:Proc_macro2.tokenStream_t = _s in
        let hoist180:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist179 Proc_macro2.Brace hoist178
        in
        let _s:Proc_macro2.tokenStream_t = hoist180 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#pub" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_le_bytes" in
        let hoist182:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let hoist181:Proc_macro2.tokenStream_t = _s in
        let hoist183:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist182 Proc_macro2.Parenthesis hoist181
        in
        let _s:Proc_macro2.tokenStream_t = hoist183 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let hoist185:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist184:Proc_macro2.tokenStream_t = _s in
        let hoist186:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist185 Proc_macro2.Bracket hoist184
        in
        let _s:Proc_macro2.tokenStream_t = hoist186 in
        let hoist194:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "pad" in
        let hoist191:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist188:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist187:Proc_macro2.tokenStream_t = _s in
        let hoist189:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist188 Proc_macro2.Parenthesis hoist187
        in
        let _s:Proc_macro2.tokenStream_t = hoist189 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_bytes_le" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist190:Proc_macro2.tokenStream_t = _s in
        let hoist192:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist191 Proc_macro2.Parenthesis hoist190
        in
        let _s:Proc_macro2.tokenStream_t = hoist192 in
        let hoist193:Proc_macro2.tokenStream_t = _s in
        let hoist195:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist194 Proc_macro2.Brace hoist193
        in
        let _s:Proc_macro2.tokenStream_t = hoist195 in
        let hoist196:Proc_macro2.tokenStream_t = _s in
        let hoist198:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist197 Proc_macro2.Brace hoist196
        in
        let _s:Proc_macro2.tokenStream_t = hoist198 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "pad" in
        let hoist203:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let hoist200:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let hoist199:Proc_macro2.tokenStream_t = _s in
        let hoist201:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist200 Proc_macro2.Bracket hoist199
        in
        let _s:Proc_macro2.tokenStream_t = hoist201 in
        let hoist202:Proc_macro2.tokenStream_t = _s in
        let hoist204:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist203 Proc_macro2.Parenthesis hoist202
        in
        let _s:Proc_macro2.tokenStream_t = hoist204 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let hoist206:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist205:Proc_macro2.tokenStream_t = _s in
        let hoist207:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist206 Proc_macro2.Bracket hoist205
        in
        let _s:Proc_macro2.tokenStream_t = hoist207 in
        let hoist218:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#mut" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let hoist209:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0u8" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist208:Proc_macro2.tokenStream_t = _s in
        let hoist210:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist209 Proc_macro2.Bracket hoist208
        in
        let _s:Proc_macro2.tokenStream_t = hoist210 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "upper" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "lower" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "upper" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_sub _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist212:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "lower" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "upper" in
        let hoist211:Proc_macro2.tokenStream_t = _s in
        let hoist213:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist212 Proc_macro2.Bracket hoist211
        in
        let _s:Proc_macro2.tokenStream_t = hoist213 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "copy_from_slice" in
        let hoist215:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "bytes" in
        let hoist214:Proc_macro2.tokenStream_t = _s in
        let hoist216:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist215 Proc_macro2.Parenthesis hoist214
        in
        let _s:Proc_macro2.tokenStream_t = hoist216 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist217:Proc_macro2.tokenStream_t = _s in
        let hoist219:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist218 Proc_macro2.Brace hoist217
        in
        let _s:Proc_macro2.tokenStream_t = hoist219 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "From" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_gt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist251:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from" in
        let hoist221:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let hoist220:Proc_macro2.tokenStream_t = _s in
        let hoist222:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist221 Proc_macro2.Parenthesis hoist220
        in
        let _s:Proc_macro2.tokenStream_t = hoist222 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist248:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "max_value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "assert" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist230:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_le _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist224:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "max_value" in
        let hoist223:Proc_macro2.tokenStream_t = _s in
        let hoist225:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist224 Proc_macro2.Parenthesis hoist223
        in
        let _s:Proc_macro2.tokenStream_t = hoist225 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "\"{} is too large for type {}!\""
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "stringify" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist227:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "$" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "ident" in
        let hoist226:Proc_macro2.tokenStream_t = _s in
        let hoist228:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist227 Proc_macro2.Parenthesis hoist226
        in
        let _s:Proc_macro2.tokenStream_t = hoist228 in
        let hoist229:Proc_macro2.tokenStream_t = _s in
        let hoist231:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist230 Proc_macro2.Parenthesis hoist229
        in
        let _s:Proc_macro2.tokenStream_t = hoist231 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "repr" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_bytes_be" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#if" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "repr" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_gt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist239:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "panic" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist236:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.parse _s "\"{} is too large for type {}\""
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "x" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "stringify" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist233:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist232:Proc_macro2.tokenStream_t = _s in
        let hoist234:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist233 Proc_macro2.Parenthesis hoist232
        in
        let _s:Proc_macro2.tokenStream_t = hoist234 in
        let hoist235:Proc_macro2.tokenStream_t = _s in
        let hoist237:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist236 Proc_macro2.Parenthesis hoist235
        in
        let _s:Proc_macro2.tokenStream_t = hoist237 in
        let hoist238:Proc_macro2.tokenStream_t = _s in
        let hoist240:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist239 Proc_macro2.Brace hoist238
        in
        let _s:Proc_macro2.tokenStream_t = hoist240 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist245:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "pad" in
        let hoist242:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "repr" in
        let hoist241:Proc_macro2.tokenStream_t = _s in
        let hoist243:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist242 Proc_macro2.Parenthesis hoist241
        in
        let _s:Proc_macro2.tokenStream_t = hoist243 in
        let hoist244:Proc_macro2.tokenStream_t = _s in
        let hoist246:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist245 Proc_macro2.Brace hoist244
        in
        let _s:Proc_macro2.tokenStream_t = hoist246 in
        let hoist247:Proc_macro2.tokenStream_t = _s in
        let hoist249:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist248 Proc_macro2.Brace hoist247
        in
        let _s:Proc_macro2.tokenStream_t = hoist249 in
        let hoist250:Proc_macro2.tokenStream_t = _s in
        let hoist252:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist251 Proc_macro2.Brace hoist250
        in
        let _s:Proc_macro2.tokenStream_t = hoist252 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "core" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "convert" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "AsRef" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lt _s in
        let hoist254:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let hoist253:Proc_macro2.tokenStream_t = _s in
        let hoist255:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist254 Proc_macro2.Bracket hoist253
        in
        let _s:Proc_macro2.tokenStream_t = hoist255 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_gt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist266:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "as_ref" in
        let hoist257:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let hoist256:Proc_macro2.tokenStream_t = _s in
        let hoist258:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist257 Proc_macro2.Parenthesis hoist256
        in
        let _s:Proc_macro2.tokenStream_t = hoist258 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let hoist260:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "u8" in
        let hoist259:Proc_macro2.tokenStream_t = _s in
        let hoist261:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist260 Proc_macro2.Bracket hoist259
        in
        let _s:Proc_macro2.tokenStream_t = hoist261 in
        let hoist263:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist262:Proc_macro2.tokenStream_t = _s in
        let hoist264:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist263 Proc_macro2.Brace hoist262
        in
        let _s:Proc_macro2.tokenStream_t = hoist264 in
        let hoist265:Proc_macro2.tokenStream_t = _s in
        let hoist267:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist266 Proc_macro2.Brace hoist265
        in
        let _s:Proc_macro2.tokenStream_t = hoist267 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "core" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "fmt" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Display" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist278:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "fmt" in
        let hoist269:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "f" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#mut" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "core" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "fmt" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Formatter" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lt _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_lifetime _s "'_" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_gt _s in
        let hoist268:Proc_macro2.tokenStream_t = _s in
        let hoist270:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist269 Proc_macro2.Parenthesis hoist268
        in
        let _s:Proc_macro2.tokenStream_t = hoist270 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "core" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "fmt" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Result" in
        let hoist275:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "write" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist272:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "f" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "\"{}\"" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_hex" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist271:Proc_macro2.tokenStream_t = _s in
        let hoist273:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist272 Proc_macro2.Parenthesis hoist271
        in
        let _s:Proc_macro2.tokenStream_t = hoist273 in
        let hoist274:Proc_macro2.tokenStream_t = _s in
        let hoist276:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist275 Proc_macro2.Brace hoist274
        in
        let _s:Proc_macro2.tokenStream_t = hoist276 in
        let hoist277:Proc_macro2.tokenStream_t = _s in
        let hoist279:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist278 Proc_macro2.Brace hoist277
        in
        let _s:Proc_macro2.tokenStream_t = hoist279 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "core" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "ops" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Add" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist311:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#type" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Output" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "add" in
        let hoist281:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist280:Proc_macro2.tokenStream_t = _s in
        let hoist282:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist281 Proc_macro2.Parenthesis hoist280
        in
        let _s:Proc_macro2.tokenStream_t = hoist282 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Output" in
        let hoist308:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "lhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist284:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist283:Proc_macro2.tokenStream_t = _s in
        let hoist285:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist284 Proc_macro2.Parenthesis hoist283
        in
        let _s:Proc_macro2.tokenStream_t = hoist285 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist287:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist286:Proc_macro2.tokenStream_t = _s in
        let hoist288:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist287 Proc_macro2.Parenthesis hoist286
        in
        let _s:Proc_macro2.tokenStream_t = hoist288 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist290:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist289:Proc_macro2.tokenStream_t = _s in
        let hoist291:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist290 Proc_macro2.Parenthesis hoist289
        in
        let _s:Proc_macro2.tokenStream_t = hoist291 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let hoist293:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "lhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_add _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let hoist292:Proc_macro2.tokenStream_t = _s in
        let hoist294:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist293 Proc_macro2.Parenthesis hoist292
        in
        let _s:Proc_macro2.tokenStream_t = hoist294 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rem _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_bytes_be" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "assert" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist296:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_le _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist295:Proc_macro2.tokenStream_t = _s in
        let hoist297:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist296 Proc_macro2.Parenthesis hoist295
        in
        let _s:Proc_macro2.tokenStream_t = hoist297 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#mut" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "zero" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "offset" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_sub _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#in" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist305:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist299:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "offset" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_add _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let hoist298:Proc_macro2.tokenStream_t = _s in
        let hoist300:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist299 Proc_macro2.Bracket hoist298
        in
        let _s:Proc_macro2.tokenStream_t = hoist300 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let hoist302:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let hoist301:Proc_macro2.tokenStream_t = _s in
        let hoist303:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist302 Proc_macro2.Bracket hoist301
        in
        let _s:Proc_macro2.tokenStream_t = hoist303 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let hoist304:Proc_macro2.tokenStream_t = _s in
        let hoist306:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist305 Proc_macro2.Brace hoist304
        in
        let _s:Proc_macro2.tokenStream_t = hoist306 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist307:Proc_macro2.tokenStream_t = _s in
        let hoist309:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist308 Proc_macro2.Brace hoist307
        in
        let _s:Proc_macro2.tokenStream_t = hoist309 in
        let hoist310:Proc_macro2.tokenStream_t = _s in
        let hoist312:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist311 Proc_macro2.Brace hoist310
        in
        let _s:Proc_macro2.tokenStream_t = hoist312 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#impl" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "core" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "ops" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Mul" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens ident _s in
        let hoist344:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#type" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Output" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#fn" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "mul" in
        let hoist314:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_comma _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let hoist313:Proc_macro2.tokenStream_t = _s in
        let hoist315:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist314 Proc_macro2.Parenthesis hoist313
        in
        let _s:Proc_macro2.tokenStream_t = hoist315 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rarrow _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Output" in
        let hoist341:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "lhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist317:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist316:Proc_macro2.tokenStream_t = _s in
        let hoist318:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist317 Proc_macro2.Parenthesis hoist316
        in
        let _s:Proc_macro2.tokenStream_t = hoist318 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist320:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist319:Proc_macro2.tokenStream_t = _s in
        let hoist321:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist320 Proc_macro2.Parenthesis hoist319
        in
        let _s:Proc_macro2.tokenStream_t = hoist321 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "num_bigint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "BigUint" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "from_bytes_be" in
        let hoist323:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_and _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist322:Proc_macro2.tokenStream_t = _s in
        let hoist324:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist323 Proc_macro2.Parenthesis hoist322
        in
        let _s:Proc_macro2.tokenStream_t = hoist324 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let hoist326:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "lhs" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_star _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "rhs" in
        let hoist325:Proc_macro2.tokenStream_t = _s in
        let hoist327:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist326 Proc_macro2.Parenthesis hoist325
        in
        let _s:Proc_macro2.tokenStream_t = hoist327 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_rem _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "modulus" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "to_bytes_be" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "assert" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_bang _s in
        let hoist329:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_le _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let hoist328:Proc_macro2.tokenStream_t = _s in
        let hoist330:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist329 Proc_macro2.Parenthesis hoist328
        in
        let _s:Proc_macro2.tokenStream_t = hoist330 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#mut" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "Self" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_colon2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "zero" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#let" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "offset" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.To_tokens.ToTokens.to_tokens num_bytes _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_sub _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#for" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "r#in" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.parse _s "0" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot2 _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "len" in
        let _s:Proc_macro2.tokenStream_t =
          Quote.__private.push_group _s Proc_macro2.Parenthesis Proc_macro2.new_
        in
        let hoist338:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_dot _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist332:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "offset" in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_add _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let hoist331:Proc_macro2.tokenStream_t = _s in
        let hoist333:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist332 Proc_macro2.Bracket hoist331
        in
        let _s:Proc_macro2.tokenStream_t = hoist333 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_eq _s in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "res" in
        let hoist335:Proc_macro2.tokenStream_t = _s in
        let _s:Proc_macro2.tokenStream_t = Proc_macro2.new_ in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "i" in
        let hoist334:Proc_macro2.tokenStream_t = _s in
        let hoist336:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist335 Proc_macro2.Bracket hoist334
        in
        let _s:Proc_macro2.tokenStream_t = hoist336 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_semi _s in
        let hoist337:Proc_macro2.tokenStream_t = _s in
        let hoist339:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist338 Proc_macro2.Brace hoist337
        in
        let _s:Proc_macro2.tokenStream_t = hoist339 in
        let _s:Proc_macro2.tokenStream_t = Quote.__private.push_ident _s "value" in
        let hoist340:Proc_macro2.tokenStream_t = _s in
        let hoist342:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist341 Proc_macro2.Brace hoist340
        in
        let _s:Proc_macro2.tokenStream_t = hoist342 in
        let hoist343:Proc_macro2.tokenStream_t = _s in
        let hoist345:Proc_macro2.tokenStream_t =
          Quote.__private.push_group hoist344 Proc_macro2.Brace hoist343
        in
        let _s:Proc_macro2.tokenStream_t = hoist345 in
        let out_struct:Proc_macro2.tokenStream_t = _s in
        Core.Convert.Into.into out_struct))

let _: Prims.unit = ()