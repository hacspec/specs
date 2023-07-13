module Curve25519.X25519FIELDELEMENT_mod
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_X25519FIELDELEMENT_MODULUS: array u8 32sz =
  (let l =
      [
        127uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
        255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
        255uy; 255uy; 255uy; 255uy; 255uy; 237uy
      ]
    in
    assert_norm (List.Tot.length l == 32);
    Rust_primitives.Hax.array_of_list l)

let impl: Curve25519.Hacspec_helper.t_NatMod Curve25519.t_X25519FieldElement 32sz =
  {
    mODULUS
    =
    (fun  ->
        (let l =
            [
              127uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
              255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
              255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 237uy
            ]
          in
          assert_norm (List.Tot.length l == 32);
          Rust_primitives.Hax.array_of_list l));
    mODULUS_STR = (fun  -> "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");
    zERO = (fun  -> Rust_primitives.Hax.repeat 0uy 32sz);
    new_ = (fun (value: array u8 32sz) -> { Curve25519.X25519FieldElement.f_value = value });
    value
    =
    fun (self: Curve25519.t_X25519FieldElement) ->
      Rust_primitives.unsize self.Curve25519.X25519FieldElement.f_value
  }

let impl: Core.Convert.t_AsRef Curve25519.t_X25519FieldElement (slice u8) =
  {
    as_ref
    =
    fun (self: Curve25519.t_X25519FieldElement) ->
      Rust_primitives.unsize self.Curve25519.X25519FieldElement.f_value
  }

(* 
Last available AST for this item:

/* TO DO */
 *)

let impl: Core.Convert.t_Into Curve25519.t_X25519FieldElement (array u8 32sz) =
  {
    into = fun (self: Curve25519.t_X25519FieldElement) -> self.Curve25519.X25519FieldElement.f_value
  }

let impl: Core.Ops.Arith.t_Add Curve25519.t_X25519FieldElement Curve25519.t_X25519FieldElement =
  {
    output = Curve25519.t_X25519FieldElement;
    add
    =
    fun (self: Curve25519.t_X25519FieldElement) (rhs: Curve25519.t_X25519FieldElement) ->
      Curve25519.Hacspec_helper.NatMod.fadd self rhs
  }

let impl: Core.Ops.Arith.t_Mul Curve25519.t_X25519FieldElement Curve25519.t_X25519FieldElement =
  {
    output = Curve25519.t_X25519FieldElement;
    mul
    =
    fun (self: Curve25519.t_X25519FieldElement) (rhs: Curve25519.t_X25519FieldElement) ->
      Curve25519.Hacspec_helper.NatMod.fmul self rhs
  }

let impl: Core.Ops.Arith.t_Sub Curve25519.t_X25519FieldElement Curve25519.t_X25519FieldElement =
  {
    output = Curve25519.t_X25519FieldElement;
    sub
    =
    fun (self: Curve25519.t_X25519FieldElement) (rhs: Curve25519.t_X25519FieldElement) ->
      Curve25519.Hacspec_helper.NatMod.fsub self rhs
  }