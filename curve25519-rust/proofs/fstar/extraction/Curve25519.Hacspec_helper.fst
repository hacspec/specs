module Curve25519.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_U8 = u8

let v_U8 (x: u8) : u8 = x