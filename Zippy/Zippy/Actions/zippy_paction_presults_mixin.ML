(*  Title:      Zippy/zippy_paction_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = PAction.M.t

  type @{AllT_args} zipper = @{AllT_args} PAction.zipper
  type prio = PAction.prio

  val gen_paction_from_presults :
    (*get presults*)
    (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} PResults.presults) morph ->
    (*action when results are empty*)
    @{AllT_args} PAction.action ->
    (*update zipper with pulled result and the remaining presults*)
    @{AllT_args} result_tail_presults_action ->
    @{AllT_args} PAction.paction

  val paction_from_presults : @{ParaT_args encl = "(" ")"} PAction.Exn.ME.exn ->
    @{AllT_args} result_tail_presults_action -> @{AllT_args} PAction.paction

  val result_tail_presults_action :
    (*update with remaining presults*)
    (prio -> @{AllT_args} PResults.presults -> (@{ParaT_args} @{AllT_args} zipper, 'z) morph) ->
    (*update with pulled result*)
    (prio -> PResults.result -> (@{ParaT_args} 'z, @{AllT_args} PAction.action_result) morph) ->
    @{AllT_args} result_tail_presults_action
end

functor Zippy_PAction_PResults_Mixin(
    structure PAction_PResults : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = PAction_PResults.PAction.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_PACTION_PRESULTS_MIXIN =
struct

open PAction_PResults Log
structure MU = Zippy_Monad_Util(PAction.M); open MU MU.MB
structure Exn = Zippy_Exception_Mixin(PResults.Co)

type @{AllT_args} zipper = @{AllT_args} PAction.zipper
type prio = PAction.prio

local open SC Mo A PResults.Co Exn
in
fun gen_paction_from_presults get_presults empty_action result_tail_presults_action =
  let fun update_action rp_aco prio = AE.catch'
    (fn z => Co.resume rp_aco z
      >>= (apsnd PResults.presults #> (fn rpress => result_tail_presults_action rpress prio z)))
    (empty_action prio)
  in
    (get_presults >>> arr PResults.run_presults) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
    |> PAction.paction
  end

fun paction_from_presults exn = gen_paction_from_presults (arr PResults.L.getter)
  (Library.K (Ctxt.with_ctxt (fn ctxt =>
    (@{log Logger.DEBUG} ctxt (fn _ => "PResults empty. Disabling paction.");
    PAction.disable_paction exn >>> arr PAction.AResult.Unchanged))))

fun result_tail_presults_action update_tail_presults update_result (x, aco) prio =
  update_tail_presults prio aco >>> update_result prio x
end

end

