module Hacspec_concordium.Concordium_types.Sealed
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

class t_ContextType (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_734339128:t_ContextType v_Self
}

let impl: t_ContextType Hacspec_concordium.Concordium_types.t_InitContextExtern =
  { __marker_trait = () }

let impl_1: t_ContextType Hacspec_concordium.Concordium_types.t_ReceiveContextExtern =
  { __marker_trait = () }