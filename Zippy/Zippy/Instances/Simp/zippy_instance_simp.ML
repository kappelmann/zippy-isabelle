(*  Title:      Zippy/zippy_instance_simp.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_SIMP =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure Simp :
  sig
    val gen_data : string -> (Proof.context -> int -> tactic) -> (Proof.context -> int -> tactic) ->
      @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
    val simp_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
    val asm_simp_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
    val full_simp_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
    val asm_full_simp_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLP.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data -> @{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co -> @{AllT_args} Tac.data
  end
end

functor Zippy_Instance_Simp(
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INSTANCE_SIMP =
struct
open Z

structure Simp =
struct
local open MU; open Mo A
in
fun gen_data tac_name safe_tac tac exn id update_result mk_cud prio_sq_co_safe prio_sq_co_unsafe =
  let
    val safe_tac_name = "safe_" ^ tac_name
    fun descr tac = Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str (implode [safe_tac_name, " ORELSE ", tac_name]),
        Pretty.block [Pretty.str "Current: ", Pretty.str tac]
      ] |> Pretty.block |> Pretty.string_of)
    val empty_action = PResults.empty_action exn
    val result_action = Result_Action.changed_goals_action update_result mk_cud
    fun unsafe_ztac ctxt = tac ctxt #> CHANGED
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS_NONE_SOME_GOAL
    val {meta = unsafe_meta, paction = unsafe_paction} = {
      empty_action = Library.K empty_action,
      meta = Mixin4.Meta.Meta.metadata (id, descr tac_name),
      result_action = result_action,
      prio_sq_co = prio_sq_co_unsafe,
      tac = Ctxt.with_ctxt (unsafe_ztac #> arr)}
      |> Tac.paction_data_from_data exn
    fun safe_ztac ctxt = safe_tac ctxt #> CHANGED
      |> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val safe_empty_action = PResults.orelse_empty_action_focus empty_action unsafe_meta unsafe_paction
    val data = {
      empty_action = safe_empty_action,
      meta = Mixin4.Meta.Meta.metadata (id, descr safe_tac_name),
      result_action = result_action,
      prio_sq_co = prio_sq_co_safe,
      tac = Ctxt.with_ctxt (safe_ztac #> arr)}
  in data end

fun simp_data x = gen_data "simp" safe_simp_tac simp_tac x
fun asm_simp_data x = gen_data "asm_simp" safe_asm_simp_tac asm_simp_tac x
fun full_simp_data x = gen_data "full_simp" safe_full_simp_tac full_simp_tac x
fun asm_full_simp_data x = gen_data "asm_full_simp" safe_asm_full_simp_tac asm_full_simp_tac x
end
end
end