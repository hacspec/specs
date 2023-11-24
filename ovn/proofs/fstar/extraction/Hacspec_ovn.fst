module Hacspec_ovn
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Group (v_Self: Type) = {
  f_group_type:Type;
  f_group_type:Concordium_contracts_common.Traits.t_Serialize v_5183569706910926426.f_group_type;
  f_group_type:Concordium_contracts_common.Traits.t_Deserial v_1888537976224086151.f_group_type;
  f_group_type:Concordium_contracts_common.Traits.t_Serial v_10320647326333630898.f_group_type;
  f_group_type:Core.Marker.t_Copy v_4543221020923779833.f_group_type;
  f_group_type:Core.Clone.t_Clone v_17761277238820538890.f_group_type;
  f_group_type:Core.Cmp.t_Eq v_6020902491195533656.f_group_type;
  f_group_type:Core.Cmp.t_PartialEq v_12217495809561341085.f_group_type
    v_10832891087211025400.f_group_type;
  f_group_type:Core.Marker.t_Sized v_11006113574502888163.f_group_type;
  f_q:u32;
  f_g:v_2435825814251343790.f_group_type;
  f_g_pow:u32 -> v_12403217412826525306.f_group_type;
  f_pow:v_17386186435278539070.f_group_type -> u32 -> v_17745298227217489689.f_group_type;
  f_one:v_14625496897574701453.f_group_type;
  f_prod:v_15803927440588513364.f_group_type -> v_8822219464673212186.f_group_type
    -> v_385434819834542306.f_group_type;
  f_inv:v_1421783649257234612.f_group_type -> v_2900833311577513391.f_group_type;
  f_div:v_15411338300132236088.f_group_type -> v_5612355442158236557.f_group_type
    -> v_1581199640938228835.f_group_type
}

type t_vals =
  | C_vals_MyVal : t_vals
  | C_vals_YourVal : u32 -> t_vals
  | C_vals_YourSecondVal : u32 -> u32 -> t_vals
  | C_vals_StrangeVal {
    f_a:u32;
    f_b:u32;
    f_c:u32
  }: t_vals

let v_ZKP (g_pow_xi xi: u32) : u32 = 0ul

let v_ZKP_one_out_of_two (g_pow_vi: u32) (vi: bool) : u32 = 32ul

let check_commitment (g_pow_xi_yi_vi zkp: u32) : bool = true

let check_valid (zkp: u32) : bool = true

let check_valid2 (g_pow_xi_yi_vi zkp: u32) : bool = true

let commit_to (x: u32) : u32 = 0ul

let n: usize = sz 20

let select_private_voting_key (random: u32) : u32 = random %! f_q

let test_v: t_vals = C_vals_YourVal 32ul <: t_vals

let test_vals (x: t_vals) : u32 =
  match x with
  | C_vals_MyVal  -> 0ul
  | C_vals_YourVal x -> x
  | C_vals_YourSecondVal x y -> y
  | C_vals_StrangeVal
    { Hacspec_ovn.Vals.f_a = a ; Hacspec_ovn.Vals.f_c = c ; Hacspec_ovn.Vals.f_b = b } ->
    c

type t_CastVoteParam = {
  f_cvp_i:u32;
  f_cvp_xi:u32;
  f_cvp_vote:bool
}

type t_RegisterParam = {
  f_rp_i:u32;
  f_rp_xi:u32
}

type t_TallyParameter = | TallyParameter : t_TallyParameter

type t_alt_test = {
  f_d:u32;
  f_e:u32;
  f_f:u32
}

type t_z_17_ = | C_z_17_ : t_z_17_

unfold
let t_G = t_z_17_

let test_alt_vals (x: t_alt_test) : u32 = match x with | { f_d = d ; f_f = f ; f_e = e } -> f

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Group_for_z_17: t_Group t_z_17_ =
  {
    f_group_type = u32;
    f_q = 17ul;
    f_g = 3ul;
    f_g_pow = (fun (x: u32) -> (f_g ^. x <: u32) %! f_q);
    f_pow = (fun (g: u32) (x: u32) -> (f_g ^. x <: u32) %! f_q);
    f_one = 1ul;
    f_prod = (fun (x: u32) (y: u32) -> (x *! y <: u32) %! f_q);
    f_inv
    =
    (fun (x: u32) ->
        let res:u32 = 0ul in
        let res:u32 =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = 1ul;
                    Core.Ops.Range.f_end = f_q
                  }
                  <:
                  Core.Ops.Range.t_Range u32)
              <:
              Core.Ops.Range.t_Range u32)
            res
            (fun res i ->
                let res:u32 = res in
                let i:u32 = i in
                let ii_computation:u32 = i in
                if (f_g_pow i <: u32) =. x
                then
                  let res:u32 = ii_computation in
                  res
                else res)
        in
        res);
    f_div = fun (x: u32) (y: u32) -> f_prod x (f_inv y <: u32)
  }

let compute_group_element_for_vote (i xi: u32) (vote: bool) (xis: t_Array u32 (sz 20)) : u32 =
  let prod1:u32 = f_one in
  let prod1:u32 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = cast (i -! 1ul <: u32) <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      prod1
      (fun prod1 j ->
          let prod1:u32 = prod1 in
          let j:usize = j in
          f_prod prod1 (xis.[ j ] <: u32) <: u32)
  in
  let prod2:u32 = f_one in
  let prod2:u32 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = cast (i +! 1ul <: u32) <: usize;
              Core.Ops.Range.f_end = n
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      prod2
      (fun prod2 j ->
          let prod2:u32 = prod2 in
          let j:usize = j in
          f_prod prod2 (xis.[ j ] <: u32) <: u32)
  in
  let v_Yi:u32 = f_div prod1 prod2 in
  f_prod (f_pow v_Yi xi <: u32) (f_g_pow (if vote then 1ul else 0ul) <: u32)

type t_OvnContractState = {
  f_g_pow_xis:t_Array (impl_Group_for_z_17).f_group_type (sz 20);
  f_zkp_xis:t_Array u32 (sz 20);
  f_commit_vis:t_Array u32 (sz 20);
  f_g_pow_xi_yi_vis:t_Array (impl_Group_for_z_17).f_group_type (sz 20);
  f_zkp_vis:t_Array u32 (sz 20);
  f_tally:u32
}

let cast_vote
      (#v_A #impl_574521470_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Core.Marker.t_Sized impl_574521470_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii2:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii3:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (ctx: impl_574521470_)
      (state: t_OvnContractState)
    : Core.Result.t_Result (v_A & t_OvnContractState) Concordium_contracts_common.Types.t_ParseError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _, out:(_ &
        Core.Result.t_Result t_CastVoteParam Concordium_contracts_common.Types.t_ParseError) =
        Concordium_contracts_common.Traits.f_get (Hacspec_concordium.Concordium_traits.f_parameter_cursor
              ctx
            <:
            _)
      in
      let* (params: t_CastVoteParam):t_CastVoteParam =
        match Core.Ops.Try_trait.f_branch out with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist1:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (v_A & t_OvnContractState)
                  Concordium_contracts_common.Types.t_ParseError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist1)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (v_A & t_OvnContractState)
                Concordium_contracts_common.Types.t_ParseError) t_CastVoteParam
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (v_A & t_OvnContractState)
                Concordium_contracts_common.Types.t_ParseError) t_CastVoteParam
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let g_pow_xi_yi_vi:u32 =
          compute_group_element_for_vote params.f_cvp_i
            params.f_cvp_xi
            params.f_cvp_vote
            state.f_g_pow_xis
        in
        let zkp_vi:u32 = v_ZKP_one_out_of_two g_pow_xi_yi_vi params.f_cvp_vote in
        let cast_vote_state_ret:t_OvnContractState = Core.Clone.f_clone state in
        let cast_vote_state_ret:t_OvnContractState =
          {
            cast_vote_state_ret with
            f_g_pow_xi_yi_vis
            =
            Rust_primitives.Hax.update_at cast_vote_state_ret.f_g_pow_xi_yi_vis
              (cast (params.f_cvp_i <: u32) <: usize)
              g_pow_xi_yi_vi
          }
          <:
          t_OvnContractState
        in
        let cast_vote_state_ret:t_OvnContractState =
          {
            cast_vote_state_ret with
            f_zkp_vis
            =
            Rust_primitives.Hax.update_at cast_vote_state_ret.f_zkp_vis
              (cast (params.f_cvp_i <: u32) <: usize)
              zkp_vi
          }
          <:
          t_OvnContractState
        in
        Core.Result.Result_Ok
        (Hacspec_concordium.Concordium_traits.f_accept, cast_vote_state_ret
          <:
          (v_A & t_OvnContractState))
        <:
        Core.Result.t_Result (v_A & t_OvnContractState)
          Concordium_contracts_common.Types.t_ParseError)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (v_A & t_OvnContractState)
            Concordium_contracts_common.Types.t_ParseError)
        (Core.Result.t_Result (v_A & t_OvnContractState)
            Concordium_contracts_common.Types.t_ParseError))

let commit_to_vote
      (#v_A #impl_574521470_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Core.Marker.t_Sized impl_574521470_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii2:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii3:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (ctx: impl_574521470_)
      (state: t_OvnContractState)
    : Core.Result.t_Result (v_A & t_OvnContractState) Concordium_contracts_common.Types.t_ParseError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _, out:(_ &
        Core.Result.t_Result t_CastVoteParam Concordium_contracts_common.Types.t_ParseError) =
        Concordium_contracts_common.Traits.f_get (Hacspec_concordium.Concordium_traits.f_parameter_cursor
              ctx
            <:
            _)
      in
      let* (params: t_CastVoteParam):t_CastVoteParam =
        match Core.Ops.Try_trait.f_branch out with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist2:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (v_A & t_OvnContractState)
                  Concordium_contracts_common.Types.t_ParseError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist2)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (v_A & t_OvnContractState)
                Concordium_contracts_common.Types.t_ParseError) t_CastVoteParam
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (v_A & t_OvnContractState)
                Concordium_contracts_common.Types.t_ParseError) t_CastVoteParam
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let _:Prims.unit =
          Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?\n"
            "{\n        for zkp in (core::iter::traits::collect::f_into_iter::<[int; 20]>(\n            proj_hacspec_ovn::f_zkp_xis(state),\n        )) {\n            {\n                let _: bool = { hacspec_ovn::check_valid(zkp) };\n                Tuple0()\n            }\n        }\n    }"

        in
        let g_pow_xi_yi_vi:u32 =
          compute_group_element_for_vote params.f_cvp_i
            params.f_cvp_xi
            params.f_cvp_vote
            state.f_g_pow_xis
        in
        let commit_vi:u32 = commit_to g_pow_xi_yi_vi in
        let commit_to_vote_state_ret:t_OvnContractState = Core.Clone.f_clone state in
        let commit_to_vote_state_ret:t_OvnContractState =
          {
            commit_to_vote_state_ret with
            f_commit_vis
            =
            Rust_primitives.Hax.update_at commit_to_vote_state_ret.f_commit_vis
              (cast (params.f_cvp_i <: u32) <: usize)
              commit_vi
          }
          <:
          t_OvnContractState
        in
        Core.Result.Result_Ok
        (Hacspec_concordium.Concordium_traits.f_accept, commit_to_vote_state_ret
          <:
          (v_A & t_OvnContractState))
        <:
        Core.Result.t_Result (v_A & t_OvnContractState)
          Concordium_contracts_common.Types.t_ParseError)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (v_A & t_OvnContractState)
            Concordium_contracts_common.Types.t_ParseError)
        (Core.Result.t_Result (v_A & t_OvnContractState)
            Concordium_contracts_common.Types.t_ParseError))

let init_ovn_contract
      (#impl_108907986_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized impl_108907986_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii1:
          Hacspec_concordium.Concordium_traits.t_HasInitContext impl_108907986_ Prims.unit)
      (_: impl_108907986_)
    : Core.Result.t_Result t_OvnContractState Hacspec_concordium.Concordium_types.t_Reject =
  Core.Result.Result_Ok
  ({
      f_g_pow_xis = Rust_primitives.Hax.repeat (f_one <: u32) (sz 20);
      f_zkp_xis = Rust_primitives.Hax.repeat 0ul (sz 20);
      f_commit_vis = Rust_primitives.Hax.repeat 0ul (sz 20);
      f_g_pow_xi_yi_vis = Rust_primitives.Hax.repeat (f_one <: u32) (sz 20);
      f_zkp_vis = Rust_primitives.Hax.repeat 0ul (sz 20);
      f_tally = 0ul
    }
    <:
    t_OvnContractState)
  <:
  Core.Result.t_Result t_OvnContractState Hacspec_concordium.Concordium_types.t_Reject

let register_vote
      (#v_A #impl_574521470_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Core.Marker.t_Sized impl_574521470_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii2:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii3:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (ctx: impl_574521470_)
      (state: t_OvnContractState)
    : Core.Result.t_Result (v_A & t_OvnContractState) Concordium_contracts_common.Types.t_ParseError =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _, out:(_ &
        Core.Result.t_Result t_RegisterParam Concordium_contracts_common.Types.t_ParseError) =
        Concordium_contracts_common.Traits.f_get (Hacspec_concordium.Concordium_traits.f_parameter_cursor
              ctx
            <:
            _)
      in
      let* (params: t_RegisterParam):t_RegisterParam =
        match Core.Ops.Try_trait.f_branch out with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist3:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (v_A & t_OvnContractState)
                  Concordium_contracts_common.Types.t_ParseError)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist3)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (v_A & t_OvnContractState)
                Concordium_contracts_common.Types.t_ParseError) t_RegisterParam
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (v_A & t_OvnContractState)
                Concordium_contracts_common.Types.t_ParseError) t_RegisterParam
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let g_pow_xi:u32 = f_g_pow params.f_rp_xi in
        let zkp_xi:u32 = v_ZKP g_pow_xi params.f_rp_xi in
        let register_vote_state_ret:t_OvnContractState = Core.Clone.f_clone state in
        let register_vote_state_ret:t_OvnContractState =
          {
            register_vote_state_ret with
            f_g_pow_xis
            =
            Rust_primitives.Hax.update_at register_vote_state_ret.f_g_pow_xis
              (cast (params.f_rp_i <: u32) <: usize)
              g_pow_xi
          }
          <:
          t_OvnContractState
        in
        let register_vote_state_ret:t_OvnContractState =
          {
            register_vote_state_ret with
            f_zkp_xis
            =
            Rust_primitives.Hax.update_at register_vote_state_ret.f_zkp_xis
              (cast (params.f_rp_i <: u32) <: usize)
              zkp_xi
          }
          <:
          t_OvnContractState
        in
        Core.Result.Result_Ok
        (Hacspec_concordium.Concordium_traits.f_accept, register_vote_state_ret
          <:
          (v_A & t_OvnContractState))
        <:
        Core.Result.t_Result (v_A & t_OvnContractState)
          Concordium_contracts_common.Types.t_ParseError)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (v_A & t_OvnContractState)
            Concordium_contracts_common.Types.t_ParseError)
        (Core.Result.t_Result (v_A & t_OvnContractState)
            Concordium_contracts_common.Types.t_ParseError))

let tally_votes
      (#v_A: Type)
      (#impl_574521470_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Core.Marker.t_Sized impl_574521470_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii2:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          ii3:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (_: impl_574521470_)
      (state: t_OvnContractState)
    : Core.Result.t_Result (v_A & t_OvnContractState) Concordium_contracts_common.Types.t_ParseError =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?\n"
      "{\n        for i in (core::iter::traits::collect::f_into_iter::<core::ops::range::t_Range<int>>(\n            core::ops::range::Range {\n                f_start: 0,\n                f_end: hacspec_ovn::n,\n            },\n        )) {\n            {\n                let _: bool = {\n                    hacspec_ovn::check_valid2(\n                        core::ops::index::Index::index(\n                            proj_hacspec_ovn::f_g_pow_xi_yi_vis(state),\n                            i,\n                        ),\n                        core::ops::index::Index::index(proj_hacspec_ovn::f_zkp_vis(state), i),\n                    )\n                };\n                {\n                    let _: bool = {\n                        hacspec_ovn::check_commitment(\n                            core::ops::index::Index::index(\n                                proj_hacspec_ovn::f_g_pow_xi_yi_vis(state),\n                                i,\n                            ),\n                            core::ops::index::Index::index(\n                                proj_hacspec_ovn::f_commit_vis(state),\n                                i,\n                            ),\n                        )\n                    };\n                    Tuple0()\n                }\n            }\n        }\n    }"

  in
  let vote_result:u32 = f_one in
  let vote_result:u32 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter state.f_g_pow_xi_yi_vis
        <:
        Core.Array.Iter.t_IntoIter u32 (sz 20))
      vote_result
      (fun vote_result g_pow_vote ->
          let vote_result:u32 = vote_result in
          let g_pow_vote:u32 = g_pow_vote in
          f_prod vote_result g_pow_vote <: u32)
  in
  let tally:u32 = 0ul in
  let tally:u32 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = 0ul;
              Core.Ops.Range.f_end = cast (n <: usize) <: u32
            }
            <:
            Core.Ops.Range.t_Range u32)
        <:
        Core.Ops.Range.t_Range u32)
      tally
      (fun tally i ->
          let tally:u32 = tally in
          let i:u32 = i in
          if (f_g_pow i <: u32) =. vote_result <: bool
          then
            let tally:u32 = i in
            tally
          else tally)
  in
  let tally_votes_state_ret:t_OvnContractState = Core.Clone.f_clone state in
  let tally_votes_state_ret:t_OvnContractState =
    { tally_votes_state_ret with f_tally = tally } <: t_OvnContractState
  in
  Core.Result.Result_Ok
  (Hacspec_concordium.Concordium_traits.f_accept, tally_votes_state_ret
    <:
    (v_A & t_OvnContractState))
  <:
  Core.Result.t_Result (v_A & t_OvnContractState) Concordium_contracts_common.Types.t_ParseError
