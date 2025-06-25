(*  Title:      Zippy/zippy_run_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUN_MIXIN =
sig
  include ZIPPY_RUN_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  sharing type M.t = PAction_Queue.PAction.M.t
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  type @{AllT_args} state
  val seq_from_monad : @{AllT_args} state -> (@{ParaT_args} 'a Seq.seq) M.t -> 'a Seq.seq

  type @{AllT_args} result_data = {
    thm_states : GClusters.GCS.state Seq.seq,
    queue : @{AllT_args} PAction_Queue.queue,
    zipper : @{AllT_args} GClusters.L.container,
    state : @{AllT_args} state}

  datatype 'a result = Finished of 'a | Unfinished of 'a
  val is_finished : 'a result -> bool
  val get_result_data : 'a result -> 'a

  (* unfinished state sequences *)
  val filter_unfinished_statesq : GClusters.GCS.state Seq.seq -> GClusters.GCS.state Seq.seq
  val mk_unreturned_statesq :
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat

  val mk_unfinished_unreturned_statesq :
    (@{ParaT_args} @{AllT_args} GCluster.L.container,
      (@{ParaT_args} unit, @{AllT_args} GClusters.L.container) Co.Co.coroutine) cat ->
    Proof.context -> (@{ParaT_args} @{AllT_args} GClusters.L.container,
      GClusters.GCS.state Seq.seq) cat

  val mk_df_post_unreturned_unfinished_statesq : Proof.context ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat
  val mk_df_post_promising_unreturned_unfinished_statesq : Proof.context ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat

  (* run *)
  type @{AllT_args} container
  val gen_repeat_step_queue : (@{AllT_args} PAction_Queue.queue ->
      (@{ParaT_args} @{AllT_args} container,
        ((@{AllT_args} GClusters.L.container * Results.results)) option
        * @{AllT_args} PAction_Queue.queue) cat) ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat ->
    int option -> @{AllT_args} PAction_Queue.queue -> @{AllT_args} state ->
    @{AllT_args} container -> @{AllT_args} result_data result Seq.seq

  val repeat_step_queue :
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat ->
    int option -> @{AllT_args} PAction_Queue.queue -> @{AllT_args} state ->
    @{AllT_args} container -> @{AllT_args} result_data result Seq.seq

  val gen_init_repeat_step_queue : (@{AllT_args} PAction_Queue.queue ->
      (@{ParaT_args} @{AllT_args} container,
        ((@{AllT_args} GClusters.L.container * Results.results)) option
        * @{AllT_args} PAction_Queue.queue) cat) ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat ->
    int option -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} result_data result Seq.seq) cat

  val init_repeat_step_queue :
    (@{ParaT_args} @{AllT_args} GClusters.L.container, GClusters.GCS.state Seq.seq) cat ->
    int option -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} result_data result Seq.seq) cat
end

functor Zippy_Run_Mixin(Args :
  sig
    structure Z : ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    structure Run : ZIPPY_RUN_MIXIN_BASE
    sharing type Run.GClusters.L.container = Z.Z1.zipper
    sharing type Run.GCluster.L.container = Z.Z2.zipper
    sharing type Run.PAction_Queue.PAction.zipper_trim = Z.Z1.zipper
    sharing type Run.PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type Run.PAction_Queue.PAction.zipper_expand = Z.Z5.zipper
    sharing type Run.Action_App_Meta.L.container = Z.Z5.zipper
    sharing type Run.PAction_Queue.PAction.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = Z.M.t
    val mk_exn : (unit -> @{ParaT_args encl = "" ""} Co.ME.exn)
    type @{AllT_args} state
    val seq_from_monad : @{AllT_args} state -> (@{ParaT_args} 'a Seq.seq) Z.M.t -> 'a Seq.seq
    val with_state : (@{AllT_args} state -> (@{ParaT_args} 'a, 'b) Z.cat) ->
      (@{ParaT_args} 'a, 'b) Z.cat
  end) : ZIPPY_RUN_MIXIN =
struct

open Args Args.Run Args.Z
structure MU = Zippy_Monad_Util(M); open MU
structure ZL = Zippy_Lists(structure Z = Z; structure Co = Co)
structure ZE = Zippy_Enum_Mixin(open Z; structure Co = Co)
structure GClusters = Zippy_Goal_Clusters_Mixin(Args.Run.GClusters)
structure GClusters_Results = Zippy_Goal_Results_Mixin(Args.Run.GClusters_Results)
structure LGoals_Results_TMV = Zippy_Lists_Goals_Results_Top_Meta_Vars_Mixin(
  structure Z = ZL; structure Goals_Results_Top_Meta_Vars = Args.Run)
structure PAction_Queue = Zippy_PAction_Queue_Mixin(
  structure Z = ZE; structure PAction_Queue = PAction_Queue; val mk_exn = mk_exn)
structure Action_App_Meta = Zippy_Action_App_Metadata_Mixin(Action_App_Meta)
structure EAction_App_Meta = Zippy_Enum_Action_App_Metadata_Mixin(
  structure Z = ZE; structure Meta = Action_App_Meta)
structure Step = Zippy_Step_Mixin(open Args; structure Step = Args.Run)

type @{AllT_args} state = @{AllT_args} state
val seq_from_monad = seq_from_monad

type @{AllT_args} result_data = {
  thm_states : GClusters.GCS.state Seq.seq,
  queue : @{AllT_args} PAction_Queue.queue,
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

fun mk_unfinished_unreturned_statesq enum_children2 ctxt =
  LGoals_Results_TMV.mk_statesq enum_children2 ctxt
  >>> arr filter_unfinished_statesq |> mk_unreturned_statesq

fun mk_df_post_unreturned_unfinished_statesq ctxt =
  mk_unfinished_unreturned_statesq (LGoals_Results_TMV.enum_df_post_children2 mk_exn) ctxt
fun mk_df_post_promising_unreturned_unfinished_statesq ctxt =
  mk_unfinished_unreturned_statesq (EAction_App_Meta.enum_df_post_promising_children2 mk_exn) ctxt

(* run *)
local
  fun result_data queue zipper state thm_states =
    {queue = queue, state = state, zipper = zipper, thm_states = thm_states}
  fun finished x = Finished ooo result_data x
  fun unfinished x = Unfinished ooo result_data x
in
type @{AllT_args} container = @{AllT_args} Z1.ZM.container
fun gen_repeat_step_queue step_queue mk_unfinished_statesq opt_fuel queue s c =
  let val case_unfinished = Z1.ZM.Zip.move
    >>> (fn z => mk_unfinished_statesq z
    >>= with_state (fn s => arr (unfinished queue z s #> Seq.single)))
  in Seq.make (fn _ => c |>
    (if the_default 1 opt_fuel <= 0 then case_unfinished
    else if PAction_Queue.Queue.is_empty queue then case_unfinished
    else Co.AE.catch'
      (step_queue queue
      >>> with_state (fn s => fn (opt_res, queue) =>
        let val nextsq = gen_repeat_step_queue step_queue mk_unfinished_statesq
          (Option.map General_Util.pred opt_fuel) queue s
        in case opt_res of
          NONE => arr nextsq c
        | SOME (z, results) => Z1.ZM.Unzip.move z >>= arr (nextsq #>
            (if Results.has_results results
            then Results.get_states results |> finished queue z s |> Seq.cons
            else I))
        end))
      (A.K Seq.empty))
    |> seq_from_monad s |> Seq.pull)
  end
end
fun repeat_step_queue x = gen_repeat_step_queue (Step.step_queue #> Ctxt.with_ctxt) x

fun gen_init_repeat_step_queue step_queue mk_unfinished_statesq opt_fuel c =
  PAction_Queue.init_pactions_queue c
  >>= with_state (fn s => arr (fn queue =>
    gen_repeat_step_queue step_queue mk_unfinished_statesq opt_fuel queue s c))
fun init_repeat_step_queue x = gen_init_repeat_step_queue (Step.step_queue #> Ctxt.with_ctxt) x
end
end
