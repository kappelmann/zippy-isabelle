(*  Title:      Zippy/zippy_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_UTIL =
sig
  (* misc *)
  val mk_exn : unit -> @{ParaT_args encl = "" ""} Zippy.Exn.ME.exn
  val run_monad : {ctxt : Proof.context, state : @{ParaT_args encl = "" ""}} ->
    (@{ParaT_args} 'a) Zippy.M.t ->
    {result : 'a, ctxt : Proof.context, state : @{ParaT_args encl = "" ""}} option

  (* nodes *)
  val node1 : Zippy.Goals.GClusters.GCS.gclusters -> @{AllT_args} Zippy.ZN.ZN.N1.node
  val node2 : Zippy.Mixin2.Top_Meta_Vars.TMV.top_meta_vars -> Zippy.Goals.GCluster.GC.gcluster ->
    @{AllT_args} Zippy.ZN.ZN.N2.node

  (* initialisation *)
  val init_thm_state : (@{ParaT_args} Zippy_Thm_State.state, @{AllT_args} Zippy.Z1.zipper) Zippy.morph

  (* action cluster *)
  val cons_action_cluster : Zippy.Mixin3.Meta.Meta.metadata ->
    (Zippy.Mixin4.Goal_Focus.F.focus * (Zippy.Mixin4.Goal_Focus.F.focus ->
      (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.morph)) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  (* presults *)
  val cons_presults_action :
    (Zippy.Mixin4.PResults.result * @{AllT_args} Zippy.Mixin4.PResults.presults ->
       @{AllT_args} Zippy.Mixin4.PAction.action) ->
    Zippy.Mixin4.Meta.Meta.metadata -> Zippy.Mixin4.Goal_Focus.F.focus ->
    @{AllT_args} Zippy.Mixin4.PResults.presults ->
    (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.morph

  (*note: results are added to the back since this keeps the paths of existing nodes unchanged.*)
  val snoc_action_application_result : Zippy.Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper, @{AllT_args} Zippy.Z5.zipper) Zippy.morph

  val update_tail_presults : @{AllT_args} Zippy.Mixin4.PResults.presults ->
    @{AllT_args} Zippy.Z4.zipper -> @{AllT_args} Zippy.Z4.zipper

  val init_result_copy_parents : Zippy.Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      Zippy.Mixin3.Copy.copy_update_data * @{AllT_args} Zippy.Z1.zipper) Zippy.morph

  val update_result : Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.Mixin4.PAction.action_result) Zippy.morph

  val result_tail_presults_action :
    Zippy.Mixin4.PResults.result * @{AllT_args} Zippy.Mixin4.PResults.presults ->
    @{AllT_args} Zippy.Mixin4.PAction.action
end

structure Zippy_Util : ZIPPY_UTIL =
struct
open Zippy Zippy.MU

(* misc *)
fun mk_exn _ = exn

fun run_monad {ctxt, state} = State_MSTrans.run state #> Ctxt_MSTrans.run ctxt
  #> Option.map (fn x =>
    let
      val ctxt = Ctxt_MSTrans.SR.state x
      val x = Ctxt_MSTrans.SR.value x
      val state = State_MSTrans.SR.state x
      val result = State_MSTrans.SR.value x
    in {result = result, ctxt = ctxt, state = state} end)

(* nodes *)
fun node1 gclusters = ZN.node_no_next1 exn {
  gclusters = gclusters,
  results = if Mixin1.GClusters.GCS.is_finished gclusters
    then Mixin1.Results.R.non_empty (Seq.single (Mixin1.GClusters.GCS.get_state gclusters))
    else Mixin1.Results.R.empty}
local open Mixin2
in
fun node2 parent_top_meta_vars gcluster = ZN.node_no_next2 exn {
  gcluster = gcluster,
  results = Results.R.empty,
  top_meta_vars = Top_Meta_Vars.TMV.init parent_top_meta_vars (GCluster.GC.get_state gcluster)}
end

local open SC Mo A
in
(* initialisation *)
fun init_thm_state state = state |>
  (LGoals_Tac.init_state
    (node1 #> ZN.container_no_parent exn #> Container_Constructor.init_container1 #> Z1.ZM.Zip.morph)
    (node2 (Zippy_Thm_State.meta_vars state))
  >>> arr snd)

(* action cluster *)
fun cons_action_cluster meta =
  LGoals_Tac_Copy_PAction.cons_action_cluster exn (fn copy => {meta = meta, copy = copy})

(* presults *)
fun cons_presults_action result_tail_presults_action meta focus presults =
  let val n = {presults = presults,
    action_app_num = Mixin4.Action_App_Num.AANum.init,
    focus = focus,
    paction = Mixin4.PAction_PResults.paction_from_presults exn result_tail_presults_action,
    meta = meta}
  in ZL.cons_content_move_safe3 exn n end

fun snoc_action_application_result prio result z =
  let
    val result_meta = Tac.get_more result
    val action_app_num = Mixin4.Action_App_Num.L.getter z
    val focus = Mixin4.Goal_Focus.L.getter z
    val n = {action_app_num = action_app_num, focus = focus, prio = prio, result_meta = result_meta}
  in ZL.snoc_content_move_safe4 exn n z end

fun update_tail_presults presults z = L.set_modify Mixin4.PResults.L.modifier (presults, z)
  |> Mixin4.Action_App_Num.inc_action_app_num

fun init_result_copy_parents prio result z =
  let fun set_next5 n z = L.set_modify ZN.Node_Next5.modifier (pure n, z)
  in
    Up4.morph z >>= Up3.morph >>= arr Mixin2.Top_Meta_Vars.L.getter >>=
    (fn parent_top_meta_vars => LGoals_Tac_Copy.init_result_copy_parents mk_exn
      (fn gclusters => snoc_action_application_result prio result
        >>> arr (set_next5 (node1 gclusters))
        >>> Down5.morph)
      (node2 parent_top_meta_vars) result z)
  end

fun update_result prio result = init_result_copy_parents prio result >>> arr snd
  >>> Ctxt.with_ctxt LGoals_Results.init_goal_results_down1 >>> arr fst
  >>> Up1.morph >>> arr Mixin4.PAction.AResult.Expand

fun result_tail_presults_action x = Mixin4.PAction_PResults.result_tail_presults_action
  (Library.K (fn presults => arr (update_tail_presults presults))) update_result x
end

end
