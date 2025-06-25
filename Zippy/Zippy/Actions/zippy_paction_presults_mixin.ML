(*  Title:      Zippy/zippy_paction_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN =
sig
  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  sharing type M.t = PAction.M.t

  type @{AllT_args} zipper = @{AllT_args} PAction.zipper
  type prio = PAction.prio

  val gen_paction_from_presults :
    (*get presults*)
    (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} PResults.presults) cat ->
    (*action when results are empty*)
    @{AllT_args} PAction.action ->
    (*update zipper with pulled result and the remaining presults*)
    (PResults.result * @{AllT_args} PResults.presults -> @{AllT_args} PAction.action) ->
    @{AllT_args} PAction.paction

  val paction_from_presults : @{ParaT_args encl = "(" ")"} PResults.Co.ME.exn ->
    (PResults.result * @{AllT_args} PResults.presults -> @{AllT_args} PAction.action) ->
    @{AllT_args} PAction.paction

  val result_tail_presults_action :
    (*update with remaining presults*)
    (prio -> @{AllT_args} PResults.presults -> (@{ParaT_args} @{AllT_args} zipper, 'z) cat) ->
    (*update with pulled result*)
    (prio -> PResults.result -> (@{ParaT_args} 'z, @{AllT_args} PAction.action_result) cat) ->
    PResults.result * @{AllT_args} PResults.presults -> @{AllT_args} PAction.action
end

functor Zippy_PAction_PResults_Mixin(
    PAction_PResults : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PACTION_PRESULTS_MIXIN =
struct

open PAction_PResults
structure MU = Zippy_Monad_Util(PAction.M); open MU MU.MB
structure Exn = Zippy_Exception_Mixin(PResults.Co)
structure PAction = Zippy_PAction_Mixin(open PAction_PResults; structure Exn = Exn)
structure PResults = Zippy_PResults_Mixin(PAction_PResults.PResults)

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

fun paction_from_presults e = gen_paction_from_presults (arr PResults.L.getter)
  (Library.K (arr (PAction.disable_paction e #> PAction.AResult.Stagnate)))

fun result_tail_presults_action update_tail_presults update_result (x, aco) prio =
  update_tail_presults prio aco >>> update_result prio x
end

end

