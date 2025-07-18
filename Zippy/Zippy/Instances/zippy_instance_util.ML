(*  Title:      Zippy/zippy_instance_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_UTIL =
sig
  (* misc *)
  val mk_exn : unit -> @{ParaT_args encl = "" ""} Zippy.Exn.ME.exn
  val run_monad : {ctxt : Proof.context, state : @{ParaT_args encl = "" ""}} ->
    (@{ParaT_args} 'a) Zippy.M.t ->
    {result : 'a, ctxt : Proof.context, state : @{ParaT_args encl = "" ""}} option

  (* nodes *)
  val node_co1 : Zippy.Goals.GClusters.GCS.gclusters -> @{AllT_args} Zippy.ZN.ZN.N1.content
  val node_co2 : Zippy.Mixin2.Top_Meta_Vars.TMV.top_meta_vars -> Zippy.Goals.GCluster.GC.gcluster ->
    @{AllT_args} Zippy.ZN.ZN.N2.content
  val node_co3 : Zippy.Mixin3.Meta.Meta.metadata -> @{AllT_args} Zippy.Mixin3.Copy.copy ->
    @{AllT_args} Zippy.ZN.ZN.N3.content
  val node_co4 : @{AllT_args} Zippy.Mixin4.PAction_PResults.result_tail_presults_action ->
    Zippy.Mixin4.Meta.Meta.metadata -> Zippy.Mixin4.Goal_Focus.F.focus ->
    @{AllT_args} Zippy.Mixin4.PResults.presults -> @{AllT_args} Zippy.ZN.ZN.N4.content
  val node_co5 : Zippy.Prio.prio -> Zippy.Mixin4.PResults.result -> @{AllT_args} Zippy.Z4.zipper ->
    @{AllT_args} Zippy.ZN.ZN.N5.content

  (* initialisation *)
  val init_thm_state : (@{ParaT_args} Zippy_Thm_State.state, @{AllT_args} Zippy.Z1.zipper) Zippy.morph

  (* action cluster *)
  val cons_action_cluster : Zippy.Mixin3.Meta.Meta.metadata ->
    (Zippy.Mixin4.Goal_Focus.F.focus * (Zippy.Mixin4.Goal_Focus.F.focus ->
      (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper) Zippy.emorph)) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  (* copy update data *)
  type @{AllT_args} mk_copy_update_data = Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z1.zipper, Zippy.Mixin3.Copy.copy_update_data) Zippy.morph

  val copy_update_data : @{AllT_args} mk_copy_update_data
  val copy_update_data_changed :
    (Zippy.Tac.GPU.GCS.goal_pos list -> Zippy.Tac.GPU.GCS.goal_pos Zippy.Tac.GPU.T.target) ->
    @{AllT_args} mk_copy_update_data
  val copy_update_data_empty_changed : @{AllT_args} mk_copy_update_data

  (* presults action *)
  val cons_presults_action :
    @{AllT_args} Zippy.Mixin4.PAction_PResults.result_tail_presults_action ->
    Zippy.Mixin4.Meta.Meta.metadata -> Zippy.Mixin4.Goal_Focus.F.focus ->
    @{AllT_args} Zippy.Mixin4.PResults.presults ->
    (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.morph

  (*note: results are added to the back since this keeps the paths of existing nodes unchanged.*)
  val snoc_action_application_result : Zippy.Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper, @{AllT_args} Zippy.Z5.zipper) Zippy.morph

  val update_tail_presults : @{AllT_args} Zippy.Mixin4.PResults.presults ->
    @{AllT_args} Zippy.Z4.zipper -> @{AllT_args} Zippy.Z4.zipper

  val result_tail_presults_action :
    (Zippy.Prio.prio -> Zippy.Mixin4.PResults.result -> (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.Mixin4.PAction.action_result) Zippy.morph) ->
    @{AllT_args} Zippy.Mixin4.PAction_PResults.result_tail_presults_action

  val init_result : Zippy.Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper, @{AllT_args} Zippy.Z1.zipper) Zippy.morph

  val init_result_copy_parents : @{AllT_args} mk_copy_update_data -> Zippy.Prio.prio ->
    Zippy.Mixin4.PResults.result -> (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.Z1.zipper) Zippy.morph

  val update_result :
    (Zippy.Mixin4.PResults.result -> (@{ParaT_args} @{AllT_args} Zippy.Z1.zipper) Zippy.emorph) ->
    @{AllT_args} mk_copy_update_data -> Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.Mixin4.PAction.action_result) Zippy.morph

  val changed_goals_update_result :
    ((Zippy.Tac.GPU.GCS.goal_pos * Zippy.Tac.GPU.GCS.gcpos list) list ->
      (@{ParaT_args} @{AllT_args} Zippy.Z1.zipper) Zippy.emorph) ->
    @{AllT_args} mk_copy_update_data -> Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.Mixin4.PAction.action_result) Zippy.morph

  val hom_changed_goals_update_result :
    (Zippy.Tac.GPU.GCS.goal_pos ->
      (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper) Zippy.emorph) list ->
    @{AllT_args} mk_copy_update_data -> Prio.prio -> Zippy.Mixin4.PResults.result ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper,
      @{AllT_args} Zippy.Mixin4.PAction.action_result) Zippy.morph
end

structure Zippy_Instance_Util : ZIPPY_INSTANCE_UTIL =
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
local open Mixin1
in
fun node_co1 gclusters = {
  gclusters = gclusters,
  results = if GClusters.GCS.is_finished gclusters
    then Results.R.non_empty (Seq.single (GClusters.GCS.get_state gclusters))
    else Results.R.empty}
end
fun node_no_next1 gclusters = ZN.node_no_next1 exn (node_co1 gclusters)

local open Mixin2
in
fun node_co2 parent_top_meta_vars gcluster = {
  gcluster = gcluster,
  results = Results.R.empty,
  top_meta_vars = Top_Meta_Vars.TMV.init parent_top_meta_vars (GCluster.GC.get_state gcluster)}
end
fun node_no_next2 parent_top_meta_vars gcluster = ZN.node_no_next2 exn
  (node_co2 parent_top_meta_vars gcluster)

fun node_co3 meta copy = {meta = meta, copy = copy}
local open Mixin4
in
fun node_co4 result_tail_presults_action meta focus presults = {
  presults = presults,
  action_app_num = Action_App_Num.AANum.init,
  focus = focus,
  paction = PAction_PResults.paction_from_presults exn result_tail_presults_action,
  meta = meta}
end

fun node_co5 prio {gpos_update, more,...} z =
  let
    val action_app_num = Mixin4.Action_App_Num.L.getter z
    val focus = Mixin4.Goal_Focus.L.getter z
  in
    {action_app_num = action_app_num, focus = focus, prio = prio, gpos_update = gpos_update,
    result_meta = more}
  end

local open SC Mo A
in
(* initialisation *)
fun init_thm_state state = LGoals.init_state
  (node_no_next1 #> ZN.container_no_parent exn #> Container_Constructor.init_container1
    #> Z1.ZM.Zip.morph)
  (node_no_next2 (Zippy_Thm_State.meta_vars state)) state

(* action cluster *)
fun cons_action_cluster meta = LGoals_Pos_Copy.cons_action_cluster exn (node_co3 meta)

(* copy update data *)
type @{AllT_args} mk_copy_update_data = Mixin4.PResults.result ->
  (@{ParaT_args} @{AllT_args} Z1.zipper, Mixin3.Copy.copy_update_data) morph

local open Tac
  fun wrap f x z = pure (f (#gpos_update x) (Mixin1.GClusters.L.getter z))
in
fun copy_update_data x = wrap Goals_Pos_Copy.copy_update_data x
fun copy_update_data_changed update = wrap (Goals_Pos_Copy.copy_update_data_changed update)
fun copy_update_data_empty_changed x = wrap Goals_Pos_Copy.copy_update_data_empty_changed x
end

(* presults action *)
fun cons_presults_action result_tail_presults_action meta focus presults =
  ZL.cons_content_move_safe3 exn (node_co4 result_tail_presults_action meta focus presults)

fun snoc_action_application_result prio res z =
  ZL.snoc_content_move_safe4 exn (node_co5 prio res z) z

fun update_tail_presults presults z = L.set_modify Mixin4.PResults.L.modifier (presults, z)
  |> Mixin4.Action_App_Num.inc_action_app_num

fun result_tail_presults_action x = Mixin4.PAction_PResults.result_tail_presults_action
  (Library.K (update_tail_presults #> arr)) x

fun init_result prio result z =
  let fun set_next5 n z = L.set_modify ZN.Node_Next5.modifier (pure n, z)
  in
    Up4.morph z >>= Up3.morph >>= arr Mixin2.Top_Meta_Vars.L.getter
    >>= (fn parent_top_meta_vars => snoc_action_application_result prio result z
    >>= (fn z => LGoals.init_state (fn gcs => arr (set_next5 (node_no_next1 gcs)) z >>= Down5.morph)
      (node_no_next2 parent_top_meta_vars) (#state result)))
  end

fun init_result_copy_parents mk_cud prio result = init_result prio result
  >>> (fn z => mk_cud result z
  >>= (fn cud => Mixin3.ECopy.copy_parents mk_exn cud z))

fun update_result update mk_cud prio result = init_result_copy_parents mk_cud prio result
  >>> update result
  >>> Ctxt.with_ctxt LGoals_Results.init_goal_results_down1 >>> arr fst
  >>> Up1.morph >>> arr Mixin4.PAction.AResult.Expanded

fun changed_goals_update_result update = update_result
  (#gpos_update #> LGoals_Pos_Copy.update_changed_goals_gclusters_gclusters update)

fun hom_changed_goals_update_result updates = update_result
  (#gpos_update #> LGoals_Pos_Copy.update_hom_changed_goals_gclusters_gclusters updates)

end
end
