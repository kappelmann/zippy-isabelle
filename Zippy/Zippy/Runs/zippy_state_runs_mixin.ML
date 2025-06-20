(*  Title:      Zippy/zippy_state_runs_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_STATE_RUNS_MIXIN =
sig
  include ZIPPY_RUNS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  val seq_from_monad : @{ParaT_arg 0} -> (@{ParaT_args} 'a Seq.seq) M.t -> 'a Seq.seq

  type @{AllT_args} container
  type @{AllT_args} result_state = {queue : @{AllT_args} PAction_Queue.queue,
    state : @{ParaT_arg 0},
    zipper : @{AllT_args} GClusters.L.container}
  val repeat_step_queue : (@{ParaT_arg 0} -> Proof.context) -> int option ->
    @{AllT_args} PAction_Queue.queue -> @{ParaT_arg 0} -> @{AllT_args} container ->
    (GClusters.GCS.state * @{AllT_args} result_state) Seq.seq
  val init_repeat_step_queue : (@{ParaT_arg 0} -> Proof.context) -> int option ->
    (@{ParaT_args} @{AllT_args} container,
      (GClusters.GCS.state * @{AllT_args} result_state) Seq.seq) cat
end

functor Zippy_State_Runs_Mixin(Args :
  sig
    structure Z : ZIPPY_LISTS_STATE_POSITIONS_MIXIN_BASE
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
    sharing type Co.AE.exn = Z.ZN_AZ2.L.M.exn
    structure Runs : ZIPPY_RUNS_MIXIN_BASE
    where type (@{ParaT_args} 'a) PAction_Queue.PAction.M.t = (@{ParaT_args} 'a) Z.M.t
    sharing type Runs.GClusters.L.container = Z.Z1.zipper
    sharing type Runs.GCluster.L.container = Z.Z2.zipper
    sharing type Runs.PAction_Queue.PAction.zipper_trim = Z.Z1.zipper
    sharing type Runs.PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type Runs.PAction_Queue.PAction.zipper_expand = Z.Z5.zipper
    val mk_exn : (unit -> @{ParaT_args encl = "" ""} Co.AE.exn)
    val seq_from_monad : (@{ParaT_args} 'a Seq.seq) Z.ZS.MS.M.t -> 'a Seq.seq
  end
  ) : ZIPPY_STATE_RUNS_MIXIN =
struct

open Args Args.Runs Args.Z
structure MU = Zippy_Monad_Util(M); open MU
structure ZL = Zippy_Lists(structure Z = Z; structure Co = Co); open ZL
structure ZE = Zippy_Base_Enum(structure Z = Z; structure Co = Co)
structure ZS = Zippy_State_Mixin(ZS)
structure PAction_Queue = Zippy_PAction_Queue_Mixin(
  structure Z = ZE; structure PAction_Queue = PAction_Queue; val mk_exn = mk_exn)
structure Runs = Zippy_Runs_Mixin(
  structure Z = Z; structure Co = Co; structure Runs = Runs; val mk_exn = mk_exn)

type @{AllT_args} container = @{AllT_args} Runs.container
type @{AllT_args} result_state = {queue : @{AllT_args} PAction_Queue.queue,
  state : @{ParaT_arg 0},
  zipper : @{AllT_args} GClusters.L.container}

local open SC Mo A
in
fun seq_from_monad s = ZS.MS.eval s #> Args.seq_from_monad

fun repeat_step_queue sel_ctxt opt_fuel queue s c = Seq.make (fn _ => Seq.pull
  (if the_default 1 opt_fuel <= 0 then Seq.empty
  else if PAction_Queue.Queue.is_empty queue then Seq.empty
  else AE.catch'
    (ZS.with_state sel_ctxt (Runs.step_queue queue)
    >>> ZS.with_state' (fn s => fn (opt_res, queue) =>
      let val nextsq = repeat_step_queue sel_ctxt (Option.map General_Util.pred opt_fuel)
        queue s
      in case opt_res of
        NONE => arr nextsq c
      | SOME (z, results) => Z1.ZM.Unzip.move z >>= arr (nextsq #>
          (if Results.has_results results
          then Results.get_states results
            |> Seq.map (rpair {queue = queue, state = s, zipper = z})
            |> Seq.append
          else I))
      end))
    (A.K Seq.empty) c
    |> seq_from_monad s))

fun init_repeat_step_queue sel_ctxt opt_fuel c = PAction_Queue.init_pactions_queue c
  >>= ZS.with_state' (fn s => arr (fn queue => repeat_step_queue sel_ctxt opt_fuel queue s c))
end

end


