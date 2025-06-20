(*  Title:      Zippy/zippy_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_UTIL =
sig
  (* misc *)
  val mk_exn : unit -> @{ParaT_args encl = "" ""} Zippy.ZE.AE.exn

  (* nodes *)
  val node1 : Zippy.Goals.GClusters.GCS.gclusters -> @{AllT_args} Zippy.ZN.ZN.N1.node
  val node2 : Zippy.NCo2.Top_Meta_Vars.TMV.top_meta_vars -> Zippy.Goals.GCluster.GC.gcluster ->
    @{AllT_args} Zippy.ZN.ZN.N2.node

  (* initialisation *)
  val init_thm_state : (@{ParaT_args} Zippy_Thm_State.state, @{AllT_args} Zippy.Z1.zipper) Zippy.cat

  (* action cluster *)
  val cons_action_cluster : Zippy.NCo3.Meta.Meta.metadata ->
    ((Zippy.Tac.GPU.F.focus ->
      (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.cat)
      * Zippy.Tac.GPU.F.focus) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.cat

  (* presults *)
  val cons_presults_action :
    (Zippy.NCo4.PResults.result * @{AllT_args} Zippy.NCo4.PResults.presults ->
       @{AllT_args} Zippy.NCo4.PAction.action) ->
    Zippy.NCo4.Meta.Meta.metadata -> Zippy.Tac.GPU.F.focus ->
    @{AllT_args} Zippy.NCo4.PResults.presults ->
    (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.cat

  val cons_action_application_result : Zippy.Prio.prio -> Zippy.NCo4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper, @{AllT_args} Zippy.Z5.zipper) Zippy.cat

  val update_tail_presults : @{AllT_args} Zippy.NCo4.PResults.presults ->
    @{AllT_args} Zippy.Z4.zipper -> @{AllT_args} Zippy.Z4.zipper

  val init_result_copy_parents : Zippy.Prio.prio -> Zippy.NCo4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      Zippy.NCo3.Copy.copy_update_data * @{AllT_args} Zippy.Z1.zipper) Zippy.cat

  val update_result : (@{ParaT_arg 0} -> Proof.context) -> Prio.prio ->
    Zippy.NCo4.PResults.result -> (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.NCo4.PAction.action_result) Zippy.cat

  val result_tail_presults_action : (@{ParaT_arg 0} -> Proof.context) ->
    Zippy.NCo4.PResults.result * @{AllT_args} Zippy.NCo4.PResults.presults ->
    @{AllT_args} Zippy.NCo4.PAction.action

  (* finish *)
  val finish_promising_gclusters_oldest_first : Proof.context ->
    (@{ParaT_args} @{AllT_args} Zippy.Goals.GClusters.L.container, thm Seq.seq) Zippy.cat
  val finish_promising_gclusters_newest_first : Proof.context ->
    (@{ParaT_args} @{AllT_args} Zippy.Goals.GClusters.L.container, thm Seq.seq) Zippy.cat
end

structure Zippy_Util : ZIPPY_UTIL =
struct
open Zippy Zippy.MEU

(* misc *)
fun mk_exn _ = exn

(* nodes *)
fun node1 gclusters = ZN.node_no_next1 exn {
  gclusters = gclusters,
  results = if NCo1.GClusters.GCS.is_finished gclusters
    then NCo1.Results.R.non_empty (Seq.single (NCo1.GClusters.GCS.get_state gclusters))
    else NCo1.Results.R.empty}
local open NCo2
in
fun node2 parent_top_meta_vars gcluster = ZN.node_no_next2 exn {
  gcluster = gcluster,
  results = Results.R.empty,
  top_meta_vars = Top_Meta_Vars.TMV.init parent_top_meta_vars (GCluster.GC.get_state gcluster)}
end

local open SC Mo
in
(* initialisation *)
fun init_thm_state state = state |>
  (LGoals_Tac.init_state (node1 #> ZN.container_no_parent exn #> init_container1 #> Z1.ZM.Zip.move)
    (node2 (Zippy_Thm_State.meta_vars state))
  >>> arr snd)

(* action cluster *)
fun cons_action_cluster meta =
  LGTCP.cons_action_cluster exn (fn copy => {meta = meta, copy = copy})

(* presults *)
fun cons_presults_action result_tail_presults_action meta focus presults =
  let val n = {presults = presults,
    action_app_num = NCo4.ActionAN.AAN.init,
    focus = focus,
    paction = NCo4.PAction_PResults.paction_from_presults exn result_tail_presults_action,
    meta = meta}
  in ZL.cons_content_move_safe3 exn n end

fun cons_action_application_result prio result z =
  let
    val result_meta = Tac.get_more result
    val action_app_num = NCo4.ActionAN.L.getter z
    val focus = NCo4.Goal_Focus.L.getter z
    val n = {action_app_num = action_app_num, focus = focus, prio = prio, result_meta = result_meta}
  in ZL.cons_content_move_safe4 exn n z end

fun update_tail_presults presults z = L.set_modify NCo4.PResults.L.modifier (presults, z)
  |> NCo4.ActionAN.inc_action_app_num

fun init_result_copy_parents prio result z =
  let fun set_next5 n z = L.set_modify ZN.Node_Next5.modifier (pure n, z)
  in
    Up4.move z >>= Up3.move >>= arr NCo2.Top_Meta_Vars.L.getter >>=
    (fn parent_top_meta_vars => LGTC.init_result_copy_parents mk_exn
      (fn gclusters => cons_action_application_result prio result
        >>> arr (set_next5 (node1 gclusters))
        >>> Down5.move)
      (node2 parent_top_meta_vars) result z)
  end

fun update_result get_ctxt prio result = init_result_copy_parents prio result >>> arr snd
  >>> ZS.with_state get_ctxt LGoals_Results.init_goal_results_down1 >>> arr fst
  >>> Up1.move >>> arr NCo4.PAction.AResult.Expand

fun result_tail_presults_action get_ctxt = NCo4.PAction_PResults.result_tail_presults_action
  (K (fn presults => arr (update_tail_presults presults))) (update_result get_ctxt)

(* finish *)
fun list_promising_zipper5_gclusters_children z =
  arr NCo5.Result_Meta.Progress.getter z
  >>= (fn progress => (if progress = Zippy_Tactic_Result_Progress.Promising
    then Down5.move z >>= ZL.list_container_zippers1
    else pure []))
\<^imap>\<open>\<open>{i}\<close> => \<open>
and list_promising_zipper{i}_gclusters_children x = x |>
  (Down{i}.move
  >>> ZL.list_container_zippers\<^eval>\<open>succ_mod_nzippers {i}\<close>
  >>> ZB.LT.traverse (AE.catch'
    list_promising_zipper\<^eval>\<open>succ_mod_nzippers {i}\<close>_gclusters_children (A.K []))
  >>> arr List.concat)\<close>
where start = 2 and stop = 4\<close>

local
  fun finish_gclusters x = LGoals.finish_gclusters_fold list_promising_zipper2_gclusters_children x
  fun apply_append f x acc = f x >>= arr (Seq.append acc)
  fun fold_newest_first_append f = ZL.fold_newest_first (apply_append f)
  fun fold_oldest_first_append f = ZL.fold_oldest_first (apply_append f)
in
fun finish_promising_gclusters_oldest_first x = finish_gclusters fold_oldest_first_append x
fun finish_promising_gclusters_newest_first x = finish_gclusters fold_newest_first_append x
end

end

end
