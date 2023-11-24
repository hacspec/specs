module Hacspec_concordium.Concordium_types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_ContractState = { f_current_contract_state_position:u32 }

type t_Parameter = { f_current_parameter_position:u32 }

type t_AttributesCursor = {
  f_current_attribute_cursor_position:u32;
  f_remaining_items:u16
}

type t_Logger = { f__private_logger:Prims.unit }

type t_LogError =
  | LogError_Full : t_LogError
  | LogError_Malformed : t_LogError

type t_NotPayableError = | NotPayableError : t_NotPayableError

type t_Action = { f__private_action:u32 }

let impl__tag (self: t_Action) : u32 = self.f__private_action

let v____: Prims.unit = ()

let v______refinement (error_code: Core.Num.Nonzero.t_NonZeroI32) : bool = true

type t_Reject = { f_error_code:f_error_code: Core.Num.Nonzero.t_NonZeroI32{true} }

let impl_1: Core.Default.t_Default t_Reject = { __marker_trait = () }

let t_ReceiveResult
      (#v_A: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_A)
     = Core.Result.t_Result v_A t_Reject

let t_InitResult
      (#v_S: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_S)
     = Core.Result.t_Result v_S t_Reject

type t_ExternContext
  (#v_T: Type) {| _: Core.Marker.t_Sized v_T |}
  {| _: Hacspec_concordium.Concordium_types.Sealed.t_ContextType v_T |}
  = { f_marker:Core.Marker.t_PhantomData v_T }

type t_ChainMetaExtern = | ChainMetaExtern : t_ChainMetaExtern

type t_InitContextExtern = | InitContextExtern : t_InitContextExtern

type t_ReceiveContextExtern = | ReceiveContextExtern : t_ReceiveContextExtern