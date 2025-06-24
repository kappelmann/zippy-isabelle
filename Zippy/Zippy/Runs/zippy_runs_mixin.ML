(*  Title:      Zippy/zippy_runs_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUNS_MIXIN =
sig
  include ZIPPY_RUNS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  val move_entry_if_may_take_more_results : @{AllT_args} PAction_Queue.entry ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container,
      @{AllT_args} PAction_Queue.PAction.L.container option) cat

  val update_goal_results_up_stagnate : (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper,
    @{AllT_args} GClusters.L.container * Results.results) cat
  val update_goal_results_up_expand : Proof.context ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_expand,
      @{AllT_args} GClusters.L.container * Results.results) cat
  val update_goal_results_up_trim : (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_trim,
    @{AllT_args} GClusters.L.container * Results.results) cat

  val update_stagnate : @{AllT_args} PAction_Queue.queue ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) cat
  val update_expand : @{AllT_args} PAction_Queue.queue -> Proof.context ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_expand,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) cat
  val update_trim : @{AllT_args} PAction_Queue.queue ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_trim,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) cat
  val update_action_result : @{AllT_args} PAction_Queue.queue -> Proof.context ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.action_result,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) cat

  type @{AllT_args} container
  val step_queue : @{AllT_args} PAction_Queue.queue -> Proof.context ->
    (@{ParaT_args} @{AllT_args} container,
      ((@{AllT_args} GClusters.L.container * Results.results)) option
      * @{AllT_args} PAction_Queue.queue) cat
end

functor Zippy_Runs_Mixin(
    structure Z : ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
    sharing type Co.AE.exn = Z.ZN_AZ2.L.M.exn
    structure Runs : ZIPPY_RUNS_MIXIN_BASE
    sharing type Runs.GClusters.L.container = Z.Z1.zipper
    sharing type Runs.GCluster.L.container = Z.Z2.zipper
    sharing type Runs.PAction_Queue.PAction.zipper_trim = Z.Z1.zipper
    sharing type Runs.PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type Runs.PAction_Queue.PAction.zipper_expand = Z.Z5.zipper
    sharing type Runs.PAction_Queue.PAction.M.t = Z.M.t
    val mk_exn : (unit -> @{ParaT_args encl = "" ""} Co.AE.exn)
  ) : ZIPPY_RUNS_MIXIN =
struct

open Runs Z
structure MU = Zippy_Monad_Util(M); open MU
structure ZL = Zippy_Lists(structure Z = Z; structure Co = Co); open ZL
structure ZB = Zippy_Base(structure Z = Z; structure AE = AE)
structure ZE = Zippy_Base_Enum(structure Z = Z; structure Co = Co)
structure ZP = Zippy_Positions_Mixin(structure Z = ZP; structure AE = AE)
structure LGoals_Results = Zippy_Lists_Goals_Results_Mixin(
  structure Z = ZL; structure Goals_Results = Runs)
structure PAction_Queue = Zippy_PAction_Queue_Mixin(
  structure Z = ZE; structure PAction_Queue = PAction_Queue; val mk_exn = mk_exn)
structure TMV = Zippy_Goal_Results_Top_Meta_Vars_Mixin(
  structure Z = Z
  structure Goal_Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin_Base(
    structure Results = GCluster_Results; structure Top_Meta_Vars = Top_Meta_Vars))

local open SC Mo A
in
fun move_entry_if_may_take_more_results {zipper,...} z = ZP.path_from_zipper4 zipper
  >>= (fn pos => TMV.move_path_if_may_take_more_results4 pos z)

fun update_goal_results_up_stagnate z = z |> (ZB.top4 >>> arr (rpair Results.empty))
fun update_goal_results_up_expand ctxt = Down5.move >>> LGoals_Results.update_goal_results_up ctxt
fun update_goal_results_up_trim z = z |> (ZB.top1 >>> arr (rpair Results.empty))

fun update_stagnate queue =
  update_goal_results_up_stagnate &&& (fn z => PAction_Queue.update_stagnate z queue)
fun update_expand queue ctxt =
  let fun update_queue z = PAction_Queue.update_expand
    (fn z => fn queue => Down5.move z >>= Z1.ZM.Unzip.move >>=
      (fn z => PAction_Queue.fold_children_pactions_queue z queue))
    z queue
  in update_goal_results_up_expand ctxt &&& update_queue end
fun update_trim queue = update_goal_results_up_trim &&& (fn z => PAction_Queue.update_trim z queue)
fun update_action_result queue ctxt = PAction_Queue.PAction.AResult.merge
  (update_stagnate queue) (update_expand queue ctxt) (update_trim queue)

type @{AllT_args} container = @{AllT_args} Z1.ZM.container
fun step_queue queue ctxt = case PAction_Queue.Queue.min_elem queue of
    NONE => K (NONE, queue)
  | SOME ((_, e), queue) => Z1.ZM.Zip.move
      >>> move_entry_if_may_take_more_results e
      >>> AC.opt (K (NONE, queue))
        (PAction_Queue.run_entry e >>> update_action_result queue ctxt >>> first (arr SOME))
end

end

