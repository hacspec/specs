module Curve25519.SCALAR_mod
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_SCALAR_MODULUS: array u8 32sz =
  (let l =
      [
        128uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
        0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let impl: Curve25519.Hacspec_helper.t_NatMod Curve25519.t_Scalar 32sz =
  {
    mODULUS
    =
    (fun  ->
        (let l =
            [
              128uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
              0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy
            ]
          in
          assert_norm (List.Tot.length l == 32);
          Rust_primitives.Hax.array_of_list l));
    mODULUS_STR = (fun  -> "8000000000000000000000000000000000000000000000000000000000000000");
    zERO = (fun  -> Rust_primitives.Hax.repeat 0uy 32sz);
    new_ = (fun (value: array u8 32sz) -> { Curve25519.Scalar.f_value = value });
    value = fun (self: Curve25519.t_Scalar) -> Rust_primitives.unsize self.Curve25519.Scalar.f_value
  }

let impl: Core.Convert.t_AsRef Curve25519.t_Scalar (slice u8) =
  {
    as_ref
    =
    fun (self: Curve25519.t_Scalar) -> Rust_primitives.unsize self.Curve25519.Scalar.f_value
  }

(* 
Last available AST for this item:

/* TO DO */
 *)

let impl: Core.Convert.t_Into Curve25519.t_Scalar (array u8 32sz) =
  { into = fun (self: Curve25519.t_Scalar) -> self.Curve25519.Scalar.f_value }

let impl: Core.Ops.Arith.t_Add Curve25519.t_Scalar Curve25519.t_Scalar =
  {
    output = Curve25519.t_Scalar;
    add
    =
    fun (self: Curve25519.t_Scalar) (rhs: Curve25519.t_Scalar) ->
      Curve25519.Hacspec_helper.NatMod.fadd self rhs
  }

let impl: Core.Ops.Arith.t_Mul Curve25519.t_Scalar Curve25519.t_Scalar =
  {
    output = Curve25519.t_Scalar;
    mul
    =
    fun (self: Curve25519.t_Scalar) (rhs: Curve25519.t_Scalar) ->
      Curve25519.Hacspec_helper.NatMod.fmul self rhs
  }

let impl: Core.Ops.Arith.t_Sub Curve25519.t_Scalar Curve25519.t_Scalar =
  {
    output = Curve25519.t_Scalar;
    sub
    =
    fun (self: Curve25519.t_Scalar) (rhs: Curve25519.t_Scalar) ->
      Curve25519.Hacspec_helper.NatMod.fsub self rhs
  }