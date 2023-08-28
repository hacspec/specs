module Poly1305.FIELDELEMENT_mod
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_FIELDELEMENT_MODULUS: array u8 17sz =
  (let l =
      [
        3uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
        255uy; 255uy; 255uy; 251uy
      ]
    in
    assert_norm (List.Tot.length l == 17);
    Rust_primitives.Hax.array_of_list l)

let impl: Poly1305.Hacspec_helper.t_NatMod Poly1305.t_FieldElement 17sz =
  {
    mODULUS
    =
    (fun  ->
        (let l =
            [
              3uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
              255uy; 255uy; 255uy; 255uy; 251uy
            ]
          in
          assert_norm (List.Tot.length l == 17);
          Rust_primitives.Hax.array_of_list l));
    mODULUS_STR = (fun  -> "03fffffffffffffffffffffffffffffffb");
    zERO = (fun  -> Rust_primitives.Hax.repeat 0uy 17sz);
    new_ = (fun (value: array u8 17sz) -> { Poly1305.FieldElement.f_value = value });
    value
    =
    fun (self: Poly1305.t_FieldElement) -> Rust_primitives.unsize self.Poly1305.FieldElement.f_value
  }

let impl: Core.Convert.t_AsRef Poly1305.t_FieldElement (slice u8) =
  {
    as_ref
    =
    fun (self: Poly1305.t_FieldElement) -> Rust_primitives.unsize self.Poly1305.FieldElement.f_value
  }

let impl: Core.Convert.t_Into Poly1305.t_FieldElement (array u8 17sz) =
  { into = fun (self: Poly1305.t_FieldElement) -> self.Poly1305.FieldElement.f_value }

let impl: Core.Ops.Arith.t_Add Poly1305.t_FieldElement Poly1305.t_FieldElement =
  {
    output = Poly1305.t_FieldElement;
    add
    =
    fun (self: Poly1305.t_FieldElement) (rhs: Poly1305.t_FieldElement) ->
      Poly1305.Hacspec_helper.NatMod.fadd self rhs
  }

let impl: Core.Ops.Arith.t_Mul Poly1305.t_FieldElement Poly1305.t_FieldElement =
  {
    output = Poly1305.t_FieldElement;
    mul
    =
    fun (self: Poly1305.t_FieldElement) (rhs: Poly1305.t_FieldElement) ->
      Poly1305.Hacspec_helper.NatMod.fmul self rhs
  }