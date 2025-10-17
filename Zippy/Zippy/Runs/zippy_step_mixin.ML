(*  Title:      Zippy/zippy_step_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_STEP_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_STEP_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = PAction_Queue.PAction.M.t

  val move_entry_if_may_take_more_results : @{AllT_args} PAction_Queue.entry ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container,
      @{AllT_args} PAction_Queue.PAction.L.container option) morph

  val update_goal_results_up_unchanged : (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper,
    @{AllT_args} GClusters.L.container * Results.results) morph
  val update_goal_results_up_expanded :
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_expanded,
      @{AllT_args} GClusters.L.container * Results.results) morph
  val update_goal_results_up_changed :
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_changed,
      @{AllT_args} GClusters.L.container * Results.results) morph

  val update_unchanged : @{AllT_args} PAction_Queue.queue ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) morph
  val update_expanded : @{AllT_args} PAction_Queue.queue ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_expanded,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) morph
  val update_changed : @{AllT_args} PAction_Queue.queue ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.zipper_changed,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) morph
  val update_action_result : @{AllT_args} PAction_Queue.queue ->
    (@{ParaT_args} @{AllT_args} PAction_Queue.PAction.action_result,
      (@{AllT_args} GClusters.L.container * Results.results) * @{AllT_args} PAction_Queue.queue) morph

  type @{AllT_args} container1
  val step_queue : @{AllT_args} PAction_Queue.queue -> (@{ParaT_args} @{AllT_args} container1,
      (((@{AllT_args} GClusters.L.container * Results.results)) option
      * @{AllT_args} PAction_Queue.queue) option) morph
end

functor Zippy_Step_Mixin(
    structure Z : ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    structure Step : ZIPPY_STEP_MIXIN_BASE
    sharing type Step.GClusters.L.container = Z.Z1.zipper
    sharing type Step.GCluster.L.container = Z.Z2.zipper
    sharing type Step.PAction_Queue.PAction.zipper_changed = Z.Z1.zipper
    sharing type Step.PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type Step.PAction_Queue.PAction.zipper_expanded = Z.Z5.zipper
    sharing type Step.PAction_Queue.PAction.M.t = Z.M.t
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = Z.M.t
    val mk_exn : (unit -> @{ParaT_args encl: "(" ")"} Co.ME.exn)
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t =Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_PAction_Queue : ZIPPY_LOGGER_MIXIN_BASE
    structure Show_Container1 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_Container1.t = Z.Z1.ZM.container
    structure Show1 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show1.t = Z.Z1.zipper
    structure Show4 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show4.t = Z.Z4.zipper
    structure Show_Queue_Entry : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = @{AllT_args} Step.PAction_Queue.entry
  ) : ZIPPY_STEP_MIXIN =
struct

open Step Z Log
structure MU = Zippy_Monad_Util(M); open MU
structure ZL = Zippy_Lists(structure Z = Z; structure Co = Co)
structure Exn = Zippy_Exception_Mixin(Co)
structure ZB = Zippy_Base(structure Z = Z; structure Exn = Exn)
structure ZE = Zippy_Enum_Mixin(open Z; structure Co = Co)
structure ZP = Zippy_Positions_Mixin(structure Z = ZP; structure Exn = Exn)
structure LGoals_Results = Zippy_Lists_Goals_Results_Mixin(structure Z = ZL
  structure Goals_Results = Step; structure Ctxt = Ctxt; structure Log_LGoals = Log_LGoals)
structure TMV = Zippy_Goal_Results_Top_Meta_Vars_Mixin(
  structure Z = Z
  structure Goal_Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin_Base(
    structure Results = GCluster_Results; structure Top_Meta_Vars = Top_Meta_Vars))
structure PAction_Queue = Zippy_PAction_Queue_Mixin(structure Z = ZE
  structure PAction_Queue = PAction_Queue; val mk_exn = mk_exn structure Ctxt = Ctxt
  structure Log = Log_PAction_Queue; structure Show_Container1 = Show_Container1
  structure Show1 = Show1; structure Show4 = Show4)

local open SC Mo A
in
fun move_entry_if_may_take_more_results {zipper,...} z = ZP.path_from_zipper4 zipper
  >>= (fn pos => TMV.move_path_if_may_take_more_results4 pos z)

fun update_goal_results_up_unchanged z = z |> (ZB.top4 >>> arr (rpair Results.empty))
fun update_goal_results_up_expanded z = Down5.morph z
  >>= Ctxt.with_ctxt (fn ctxt => fn z => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
        Pretty.str "Updating goal results upwards from",
        Show1.pretty ctxt z
      ] |> Pretty.block |> Pretty.string_of);
    LGoals_Results.update_goal_results_up ctxt z))
(*NB. no results are returned here; actions that change structure and create new results
must be split into actions changing just structure and just expanding nodes*)
fun update_goal_results_up_changed z = z |> (ZB.top1 >>> arr (rpair Results.empty))

(*FUTURE TODO: allow actions to manipulate queue and results themselves by putting them in a state
monad; this would allow more expressive actions, e.g. ones that change structure and expand at the
same time or ones that expand multiple nodes*)
fun update_unchanged queue = update_goal_results_up_unchanged
  &&& (fn z => PAction_Queue.update_unchanged z queue)
fun update_expanded queue =
  let fun update_queue z = PAction_Queue.update_expanded
    (fn z => fn queue => Down5.morph z >>= Z1.ZM.Unzip.morph >>=
      (fn z => PAction_Queue.insert_descendant_pactions_queue z queue))
    z queue
  in update_goal_results_up_expanded &&& update_queue end
fun update_changed queue = update_goal_results_up_changed
  &&& (fn z => PAction_Queue.update_changed z queue)
fun update_action_result queue = PAction_Queue.PAction.AResult.merge
  (update_unchanged queue) (update_expanded queue) (update_changed queue)

type @{AllT_args} container1 = @{AllT_args} PAction_Queue.container1

fun step_queue queue z = Ctxt.get_ctxt () >>= (fn ctxt => z |>
  let val _ = @{log Logger.TRACE} ctxt (fn _ => "Pulling minimal entry from queue.")
  in case PAction_Queue.Queue.min_elem queue of
    NONE => (@{log Logger.DEBUG} ctxt (fn _ => "No more entries in queue."); K NONE)
  | SOME ((_, e), queue) => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
          Pretty.str "Pulled and moving to entry",
          Show_Queue_Entry.pretty ctxt e
        ] |> Pretty.block |> Pretty.string_of);
      Z1.ZM.Zip.morph
      >>> move_entry_if_may_take_more_results e
      >>> Ctxt.with_ctxt (fn ctxt => AC.opt
        (fn _ => (@{log Logger.DEBUG} ctxt (fn _ => "Entry takes no further results.");
          pure (SOME (NONE, queue))))
        (@{log Logger.TRACE} ctxt (fn _ => "Running entry.");
          PAction_Queue.run_entry e >>> update_action_result queue >>> arr (apfst SOME #> SOME))))
  end)
end

end
