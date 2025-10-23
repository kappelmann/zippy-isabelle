(*  Title:      Zippy/zippy_instance_classical.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_CLASSICAL =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure Classical :
  sig
    val slow_step_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
    val atomize_prems_data :
      Zippy_Identifier.id -> ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} Tac.data
  end
end

functor Zippy_Instance_Classical(
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INSTANCE_CLASSICAL =
struct
open Z

structure Classical =
struct
local open MU; open A
in
fun slow_step_data exn id update_result mk_cud prio_sq_co_safe prio_sq_co_inst0
  prio_sq_co_instp prio_sq_co_unsafe =
  let
    fun descr tac = Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str "Classical.slow_step",
        Pretty.block [Pretty.str "Current: ", Pretty.str tac]
      ] |> Pretty.block |> Pretty.string_of)

    val empty_action = PAction.disable_action
    val result_action = Result_Action.changed_goals_action update_result mk_cud

    fun unsafe_ztac ctxt = Classical.appWrappers ctxt (Classical.unsafe_step_tac ctxt)
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.unclear
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
    val unsafe_data = {
      empty_action = Library.K empty_action,
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "unsafe_step"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_unsafe,
      tac = Ctxt.with_ctxt (unsafe_ztac #> arr)}
      |> Tac.paction_data_from_data exn

    fun instp_step_ztac ctxt = Classical.appWrappers ctxt (Classical.instp_step_tac ctxt)
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.unclear
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
    val instp_step_data = {
      empty_action = Library.K (PAction.update_action unsafe_data),
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "instp_step"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_instp,
      tac = Ctxt.with_ctxt (instp_step_ztac #> arr)}
      |> Tac.paction_data_from_data exn

    fun inst0_step_ztac ctxt = Classical.appWrappers ctxt (Classical.inst0_step_tac ctxt)
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
    val inst0_step_data = {
      empty_action = Library.K (PAction.update_action instp_step_data),
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "inst0_step"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_inst0,
      tac = Ctxt.with_ctxt (inst0_step_ztac #> arr)}
      |> Tac.paction_data_from_data exn

    fun safe_ztac ctxt = Classical.safe_tac ctxt |> SELECT_GOAL
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1 Tac_AAM.madd
    val data = {
      empty_action = PResults.orelse_update_action empty_action inst0_step_data,
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "safe_tac"),
      result_action = result_action,
      prio_sq_co = prio_sq_co_safe,
      tac = Ctxt.with_ctxt (safe_ztac #> arr)}
  in data end

fun atomize_prems_data id update_result mk_cud prio_sq_co =
  let
    val empty_action = PAction.disable_action
    val result_action = Result_Action.changed_goals_action update_result mk_cud

    fun ztac ctxt = Object_Logic.atomize_prems_tac ctxt #> CHANGED
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1 Tac_AAM.madd
    val data = {
      empty_action = Library.K empty_action,
      meta = Mixin_Base4.Meta.Meta.metadata (id, Lazy.value "Object_Logic.atomize_prems"),
      result_action = result_action,
      prio_sq_co = prio_sq_co,
      tac = Ctxt.with_ctxt (ztac #> arr)}
  in data end
end
end
end