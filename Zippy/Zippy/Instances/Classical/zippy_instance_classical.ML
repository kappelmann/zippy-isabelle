(*  Title:      Zippy/zippy_instance_classical.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_CLASSICAL =
sig
  include ZIPPY_INSTANCE_TAC

  structure Classical :
  sig
    val slow_step_atomize_prems_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      Zippy_Identifier.id -> @{AllT_args} PResults.prio_sq_co -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
  end
end

functor Zippy_Instance_Classical(
    structure Z : ZIPPY_INSTANCE_TAC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INSTANCE_CLASSICAL =
struct
open Z

structure Classical =
struct
local open MU; open Mo A
in
fun slow_step_atomize_prems_data exn id prio_sq_co_safe prio_sq_co_unsafe prio_sq_co_atomize_prems =
  let
    fun descr tac = Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str "Classical.slow_step ORELSE Object_Logic.atomize_prems.",
        Pretty.block [Pretty.str "Current: ", Pretty.str tac]
      ] |> Pretty.block |> Pretty.string_of)

    val empty_action = PResults.empty_action exn
    val result_action = Result_Action.action (Library.K (A.id ())) Result_Action.copy_update_data

    fun atomize_prems_ztac ctxt = Object_Logic.atomize_prems_tac ctxt #> CHANGED
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val {meta = atomize_meta, paction = atomize_paction} = {
      empty_action = Library.K empty_action,
      meta = Mixin4.Meta.Meta.metadata (id, descr "atomize_prems"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_atomize_prems,
      tac = Ctxt.with_ctxt (atomize_prems_ztac #> arr)}
      |> Tac.paction_data_from_data exn

    fun unsafe_ztac ctxt = Classical.appWrappers ctxt
        (Classical.inst_step_tac ctxt APPEND' Classical.unsafe_step_tac ctxt)
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.unclear
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS_NONE_SOME_GOAL
    val {meta = unsafe_meta, paction = unsafe_paction} = {
      empty_action = PResults.orelse_empty_action_focus empty_action atomize_meta atomize_paction,
      meta = Mixin4.Meta.Meta.metadata (id, descr "inst_step APPEND unsafe_step"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_unsafe,
      tac = Ctxt.with_ctxt (unsafe_ztac #> arr)}
      |> Tac.paction_data_from_data exn

    fun safe_ztac ctxt = Classical.safe_tac ctxt |> SELECT_GOAL
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val data = {
      empty_action = PResults.orelse_empty_action_focus empty_action unsafe_meta unsafe_paction,
      meta = Mixin4.Meta.Meta.metadata (id, descr "safe_tac"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_safe,
      tac = Ctxt.with_ctxt (safe_ztac #> arr)}
  in data end
end
end
end