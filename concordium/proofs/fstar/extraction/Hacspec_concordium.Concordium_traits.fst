module Hacspec_concordium.Concordium_traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

class t_HasParameter (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_373553659:Concordium_contracts_common.Traits.t_Read
  v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_806558213:t_HasParameter v_Self;
  f_size:v_Self -> u32
}

class t_HasChainMetadata (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_839676169:t_HasChainMetadata v_Self;
  f_slot_time:v_Self -> Concordium_contracts_common.Types.t_Timestamp
}

class t_HasPolicy (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_845917934:t_HasPolicy v_Self;
  f_identity_provider:v_Self -> u32;
  f_created_at:v_Self -> Concordium_contracts_common.Types.t_Timestamp;
  f_valid_to:v_Self -> Concordium_contracts_common.Types.t_Timestamp;
  f_next_item:v_Self -> array u8 (sz 31)
    -> (Core.Option.t_Option (Concordium_contracts_common.Types.t_AttributeTag & u8) &
        array u8 (sz 31) &
        v_Self)
}

class t_HasCommonData (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_454473913:t_HasCommonData v_Self;
  f_PolicyType:Type;
  f_PolicyType:t_HasPolicy i0.f_PolicyType;
  f_PolicyType:Core.Marker.t_Sized i0.f_PolicyType;
  f_MetadataType:Type;
  f_MetadataType:t_HasChainMetadata i0.f_MetadataType;
  f_MetadataType:Core.Marker.t_Sized i0.f_MetadataType;
  f_ParamType:Type;
  f_ParamType:Concordium_contracts_common.Traits.t_Read i0.f_ParamType;
  f_ParamType:t_HasParameter i0.f_ParamType;
  f_ParamType:Core.Marker.t_Sized i0.f_ParamType;
  f_PolicyIteratorType:Type;
  f_PolicyIteratorType:Core.Iter.Traits.Exact_size.t_ExactSizeIterator i0.f_PolicyIteratorType;
  f_PolicyIteratorType:Core.Iter.Traits.Iterator.t_Iterator i0.f_PolicyIteratorType;
  f_PolicyIteratorType:Core.Marker.t_Sized i0.f_PolicyIteratorType;
  f_policies:v_Self -> i0.f_PolicyIteratorType;
  f_metadata:v_Self -> i0.f_MetadataType;
  f_parameter_cursor:v_Self -> i0.f_ParamType
}

class t_HasInitContext (#v_Self: Type) (#v_Error: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_454473913:t_HasCommonData v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_622119999:Core.Marker.t_Sized v_Error;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_333404876:Core.Default.t_Default v_Error;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_124264501:t_HasInitContext v_Self v_Error;
  f_InitData:Type;
  f_InitData:Core.Marker.t_Sized i3.f_InitData;
  f_open:i3.f_InitData -> v_Self;
  f_init_origin:v_Self -> Concordium_contracts_common.Types.t_AccountAddress
}

class t_HasReceiveContext (#v_Self: Type) (#v_Error: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_454473913:t_HasCommonData v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_622119999:Core.Marker.t_Sized v_Error;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_333404876:Core.Default.t_Default v_Error;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_524859029:t_HasReceiveContext v_Self v_Error;
  f_ReceiveData:Type;
  f_ReceiveData:Core.Marker.t_Sized i3.f_ReceiveData;
  f_open:i3.f_ReceiveData -> v_Self;
  f_invoker:v_Self -> Concordium_contracts_common.Types.t_AccountAddress;
  f_self_address:v_Self -> Concordium_contracts_common.Types.t_ContractAddress;
  f_self_balance:v_Self -> Concordium_contracts_common.Types.t_Amount;
  f_sender:v_Self -> Concordium_contracts_common.Types.t_Address;
  f_owner:v_Self -> Concordium_contracts_common.Types.t_AccountAddress
}

class t_HasContractState (#v_Self: Type) (#v_Error: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_622119999:Core.Marker.t_Sized v_Error;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_333404876:Core.Default.t_Default v_Error;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_373553659:Concordium_contracts_common.Traits.t_Read
  v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_268178196:Concordium_contracts_common.Traits.t_Write
  v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_99959236:Concordium_contracts_common.Traits.t_Seek
  v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_34555314:t_HasContractState v_Self v_Error;
  f_ContractStateData:Type;
  f_ContractStateData:Core.Marker.t_Sized i5.f_ContractStateData;
  f_open:i5.f_ContractStateData -> v_Self;
  f_size:v_Self -> u32;
  f_truncate:v_Self -> u32 -> v_Self;
  f_reserve:v_Self -> u32 -> (bool & v_Self)
}

class t_HasLogger (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_593170002:t_HasLogger v_Self;
  f_init:v_Self;
  f_log_raw:v_Self -> slice u8
    -> (Core.Result.t_Result Prims.unit Hacspec_concordium.Concordium_types.t_LogError & v_Self);
  f_log:
      #v_S: Type ->
      {| _: Core.Marker.t_Sized v_S |} ->
      {| _: Concordium_contracts_common.Traits.t_Serial v_S |} ->
      v_Self ->
      v_S
    -> (Core.Result.t_Result Prims.unit Hacspec_concordium.Concordium_types.t_LogError & v_Self)
}

class t_HasActions (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_790365329:t_HasActions v_Self;
  f_accept:v_Self;
  f_simple_transfer:
      Concordium_contracts_common.Types.t_AccountAddress ->
      Concordium_contracts_common.Types.t_Amount
    -> v_Self;
  f_send_raw:
      Concordium_contracts_common.Types.t_ContractAddress ->
      Concordium_contracts_common.Types.t_ReceiveName ->
      Concordium_contracts_common.Types.t_Amount ->
      slice u8
    -> v_Self;
  f_and_then:v_Self -> v_Self -> v_Self;
  f_or_else:v_Self -> v_Self -> v_Self
}

class t_UnwrapAbort (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_72353824:t_UnwrapAbort v_Self;
  f_Unwrap:Type;
  f_Unwrap:Core.Marker.t_Sized i0.f_Unwrap;
  f_unwrap_abort:v_Self -> i0.f_Unwrap
}

class t_ExpectReport (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_875898860:t_ExpectReport v_Self;
  f_Unwrap:Type;
  f_Unwrap:Core.Marker.t_Sized i0.f_Unwrap;
  f_expect_report:v_Self -> string -> i0.f_Unwrap
}

class t_ExpectErrReport (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_650373357:t_ExpectErrReport v_Self;
  f_Unwrap:Type;
  f_Unwrap:Core.Marker.t_Sized i0.f_Unwrap;
  f_expect_err_report:v_Self -> string -> i0.f_Unwrap
}

class t_ExpectNoneReport (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_122739808:t_ExpectNoneReport v_Self;
  f_expect_none_report:v_Self -> string -> Prims.unit
}

class t_SerialCtx (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_728516819:t_SerialCtx v_Self;
  f_serial_ctx:
      #v_W: Type ->
      {| _: Core.Marker.t_Sized v_W |} ->
      {| _: Concordium_contracts_common.Traits.t_Write v_W |} ->
      v_Self ->
      Concordium_contracts_common.Schema.t_SizeLength ->
      v_W
    -> (Core.Result.t_Result Prims.unit i2.f_Err & v_W)
}

class t_DeserialCtx (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_529871881:Core.Marker.t_Sized v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_120498864:t_DeserialCtx v_Self;
  f_deserial_ctx:
      #v_R: Type ->
      {| _: Core.Marker.t_Sized v_R |} ->
      {| _: Concordium_contracts_common.Traits.t_Read v_R |} ->
      Concordium_contracts_common.Schema.t_SizeLength ->
      bool ->
      v_R
    -> (Core.Result.t_Result v_Self Concordium_contracts_common.Types.t_ParseError & v_R)
}