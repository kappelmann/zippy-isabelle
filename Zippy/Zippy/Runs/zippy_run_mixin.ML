(*  Title:      Zippy/zippy_run_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUN_MIXIN =
sig
  include ZIPPY_RUN_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = Step.PAction_Queue.PAction.M.t
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  type @{AllT_args} state
  val seq_from_monad : @{AllT_args} state -> (@{ParaT_args} 'a Seq.seq) M.t -> 'a Seq.seq

  type @{AllT_args} result_data = {
    thm_states : Step.GClusters.GCS.state Seq.seq,
    steps : int,
    queue : @{AllT_args} Step.PAction_Queue.queue,
    zipper : @{AllT_args} Step.GClusters.L.container,
    state : @{AllT_args} state}

  datatype 'a result = Finished of 'a | Unfinished of 'a
  val is_finished : 'a result -> bool
  val get_result_data : 'a result -> 'a

  (* unfinished state sequences *)
  val filter_unfinished_statesq : Step.GClusters.GCS.state Seq.seq ->
    Step.GClusters.GCS.state Seq.seq
  val mk_unreturned_statesq :
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph ->
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph

  val mk_unfinished_unreturned_statesq :
    (@{ParaT_args} @{AllT_args} Step.GCluster.L.container,
      (@{ParaT_args} unit, @{AllT_args} Step.GClusters.L.container) Co.Co.coroutine) morph ->
    Proof.context -> (@{ParaT_args} @{AllT_args} Step.GClusters.L.container,
      Step.GClusters.GCS.state Seq.seq) morph

  val mk_df_post_unreturned_unfinished_statesq : Proof.context ->
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph
  val mk_df_post_promising_unreturned_unfinished_statesq : Proof.context ->
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph

  (* run *)
  val gen_repeat_step_queue : (@{AllT_args} Step.PAction_Queue.queue ->
      (@{ParaT_args} @{AllT_args} Step.PAction_Queue.container1,
        (((@{AllT_args} Step.GClusters.L.container * Step.Results.results)) option
        * @{AllT_args} Step.PAction_Queue.queue) option) morph) ->
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph ->
    int option -> @{AllT_args} Step.PAction_Queue.queue -> @{AllT_args} state ->
    @{AllT_args} Step.PAction_Queue.container1 -> @{AllT_args} result_data result Seq.seq

  val repeat_step_queue :
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph ->
    int option -> @{AllT_args} Step.PAction_Queue.queue -> @{AllT_args} state ->
    @{AllT_args} Step.PAction_Queue.container1 -> @{AllT_args} result_data result Seq.seq

  val gen_init_repeat_step_queue : (@{AllT_args} Step.PAction_Queue.queue ->
      (@{ParaT_args} @{AllT_args} Step.PAction_Queue.container1,
        (((@{AllT_args} Step.GClusters.L.container * Step.Results.results)) option
        * @{AllT_args} Step.PAction_Queue.queue) option) morph) ->
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph ->
    int option -> (@{ParaT_args} @{AllT_args} Step.PAction_Queue.container1,
      @{AllT_args} result_data result Seq.seq) morph

  val init_repeat_step_queue :
    (@{ParaT_args} @{AllT_args} Step.GClusters.L.container, Step.GClusters.GCS.state Seq.seq) morph ->
    int option -> (@{ParaT_args} @{AllT_args} Step.PAction_Queue.container1,
      @{AllT_args} result_data result Seq.seq) morph
end

functor Zippy_Run_Mixin(
    structure Z : ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    structure Run : ZIPPY_RUN_MIXIN_BASE
    sharing type Run.Step.GClusters.L.container = Z.Z1.zipper
    sharing type Run.Step.GCluster.L.container = Z.Z2.zipper
    sharing type Run.Step.PAction_Queue.container1 = Z.Z1.ZM.container
    sharing type Run.Step.PAction_Queue.PAction.zipper_trim = Z.Z1.zipper
    sharing type Run.Step.PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type Run.Step.PAction_Queue.PAction.zipper_expand = Z.Z5.zipper
    sharing type Run.Action_App_Meta.L.container = Z.Z5.zipper
    sharing type Run.Step.PAction_Queue.PAction.M.t = Z.M.t
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = Z.M.t
    val mk_exn : (unit -> @{ParaT_args encl = "" ""} Co.ME.exn)
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    type @{AllT_args} state
    val seq_from_monad : @{AllT_args} state -> (@{ParaT_args} 'a Seq.seq) Z.M.t -> 'a Seq.seq
    val with_state : (@{AllT_args} state -> (@{ParaT_args} 'a, 'b) Z.morph) ->
      (@{ParaT_args} 'a, 'b) Z.morph
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_RUN_MIXIN =
struct

open Run Z Log
structure MU = Zippy_Monad_Util(M); open MU
structure Co = Co
structure ZL = Zippy_Lists(structure Z = Z; structure Co = Co)
structure ZE = Zippy_Enum_Mixin(open Z; structure Co = Co)
structure GClusters = Zippy_Goal_Clusters_Mixin(Step.GClusters)
structure GClusters_Results = Zippy_Goal_Results_Mixin(Step.GClusters_Results)
structure LGoals_Results_TMV = Zippy_Lists_Goals_Results_Top_Meta_Vars_Mixin(
  structure Z = ZL; structure Goals_Results_Top_Meta_Vars = Step)
structure Action_App_Meta = Zippy_Action_App_Metadata_Mixin(Action_App_Meta)
structure EAction_App_Meta = Zippy_Enum_Action_App_Metadata_Mixin(
  structure Z = ZE; structure Meta = Action_App_Meta)

type @{AllT_args} state = @{AllT_args} state
val seq_from_monad = seq_from_monad

type @{AllT_args} result_data = {
  thm_states : GClusters.GCS.state Seq.seq,
  steps : int,
  queue : @{AllT_args} Step.PAction_Queue.queue,
  zipper : @{AllT_args} GClusters.L.container,
  state : @{AllT_args} state}

datatype 'a result = Finished of 'a | Unfinished of 'a

fun is_finished (Finished _) = true
  | is_finished (Unfinished _) = false

fun get_result_data (Finished x) = x
  | get_result_data (Unfinished x) = x

local open SC Mo A Co
in
(* unfinished state sequences *)
fun filter_unfinished_statesq sq = Seq.filter (Zippy_Thm_State.is_finished #> not) sq
fun mk_unreturned_statesq mk_unfinished_statesq z =
  if not (GClusters.has_meta_vars z) andalso GClusters_Results.has_results z
  then pure Seq.empty (*result state already returned*)
  else mk_unfinished_statesq z (*return unfinished states*)

fun mk_unfinished_unreturned_statesq enum_gclusters_children ctxt =
  LGoals_Results_TMV.mk_statesq enum_gclusters_children ctxt
  >>> arr filter_unfinished_statesq |> mk_unreturned_statesq

fun mk_df_post_unreturned_unfinished_statesq ctxt =
  mk_unfinished_unreturned_statesq (LGoals_Results_TMV.enum_df_post_children2 mk_exn) ctxt
fun mk_df_post_promising_unreturned_unfinished_statesq ctxt =
  mk_unfinished_unreturned_statesq (EAction_App_Meta.enum_df_post_promising_children2 mk_exn) ctxt

(* run *)
local
  fun result_data steps queue zipper state thm_states =
    {steps = steps, queue = queue, state = state, zipper = zipper, thm_states = thm_states}
  fun finished x = Finished oooo result_data x
  fun unfinished x = Unfinished oooo result_data x
  structure Show = SpecCheck_Show
in
type @{AllT_args} container = @{AllT_args} Z1.ZM.container
fun pretty_fuel NONE = Pretty.str "Unlimited"
  | pretty_fuel (SOME n) = Show.int n
fun gen_repeat_step_queue step_queue mk_unfinished_statesq =
  let
    fun case_unfinished steps queue = Z1.ZM.Zip.morph
      >>> Ctxt.with_ctxt (fn ctxt => fn z =>
        (@{log Logger.DEBUG} ctxt (fn _ => "Returning unfinished state sequence.");
        mk_unfinished_statesq z)
      >>= with_state (fn s => arr (unfinished steps queue z s #> Seq.single)))
    fun run steps opt_fuel queue s c = Seq.make (fn _ => Ctxt.get_ctxt () >>= (fn ctxt => c |>
      (if the_default 1 opt_fuel <= 0
      then (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Ran out of fuel after ",
            Show.int steps,
            Pretty.str " step(s)."
        ] |> Pretty.string_of);
        case_unfinished steps queue)
      else Co.AE.catch'
        (fn c => c |>
          (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
            Pretty.str "Running one step.",
            Pretty.block [Pretty.str "Step count: ", Show.int steps, Pretty.str "."],
            Pretty.block [Pretty.str "Remaining fuel: ", pretty_fuel opt_fuel]
          ] |> Pretty.block |> Pretty.string_of);
          step_queue queue)
        >>= (fn x => x |>
          let val steps = steps + 1
          in AC.opt
            (Ctxt.with_ctxt (fn ctxt => fn _ => (@{log Logger.DEBUG} ctxt (fn _ => "Queue is empty.");
              case_unfinished steps queue c)))
            (with_state (fn s => fn (opt_res, queue) =>
              let val nextsq = run steps (Option.map General_Util.pred opt_fuel) queue s
              in case opt_res of
                NONE => Ctxt.get_ctxt () >>= (fn ctxt =>
                  (@{log Logger.DEBUG} ctxt (fn _ => "No zipper changes. Continuing with next step.");
                  arr nextsq c))
              | SOME (z, results) => Z1.ZM.Unzip.morph z
                  >>= Ctxt.with_ctxt (fn ctxt => arr (nextsq #>
                    (if Step.Results.has_results results
                    then (@{log Logger.DEBUG} ctxt (fn _ => "Returning new results.");
                      Step.Results.get_states results |> finished steps queue z s |> Seq.cons)
                    else (@{log Logger.DEBUG} ctxt (fn _ => "No new results. Continuing with next step.");
                      I))))
              end))
          end))
        (fn _ => (@{log Logger.WARN} ctxt (fn _ => "Error while running step. Stopping run.");
          pure Seq.empty))))
      |> seq_from_monad s |> Seq.pull)
  in run 0 end
end
fun repeat_step_queue x = gen_repeat_step_queue Step.step_queue x

fun gen_init_repeat_step_queue step_queue mk_unfinished_statesq opt_fuel c =
  Step.PAction_Queue.init_pactions_queue c
  >>= with_state (fn s => arr (fn queue =>
    gen_repeat_step_queue step_queue mk_unfinished_statesq opt_fuel queue s c))
fun init_repeat_step_queue x = gen_init_repeat_step_queue Step.step_queue x
end
end
