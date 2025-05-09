(*  Title:      Zippy/zippy_paction_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN =
sig
  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

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

  val paction_from_presults : @{ParaT_args encl = "(" ")"} PResults.Co.AE.exn ->
    (PResults.result * @{AllT_args} PResults.presults -> @{AllT_args} PAction.action) ->
    @{AllT_args} PAction.paction

  val gen_update_result_tail_presults :
    (*update with pulled result*)
    (prio -> PResults.result -> (@{ParaT_args} @{AllT_args} zipper, 'z) cat) ->
    (*update with remaining presults*)
    (prio -> @{AllT_args} PResults.presults -> (@{ParaT_args} 'z, @{AllT_args} zipper) cat) ->
    PResults.result * @{AllT_args} PResults.presults -> @{AllT_args} PAction.action

  (* val update_tail_presults : @{AllT_args} PResults.presults ->
    (@{ParaT_args} @{AllT_args} zipper) hom_move *)
end

functor Zippy_PAction_PResults_Mixin(
    PAction_PResults : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PACTION_PRESULTS_MIXIN =
struct

open PAction_PResults
structure U = Zippy_Monad_Util(PAction.M); open U
structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = PAction; open M
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  open PResults.Co.AE; structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli"\<close>(M))
structure PAction = Zippy_PAction_Mixin(open PAction_PResults; structure AE = AE)
structure PResults = Zippy_PResults_Mixin(open PAction_PResults AE)

type @{AllT_args} zipper = @{AllT_args} PAction.zipper
type prio = PAction.prio

local open SC Mo A
in
fun gen_paction_from_presults get_presults empty_action update_result_tail_presults =
  let fun update_action rp_aco prio = AE.catch'
    (fn z => PResults.Co.resume rp_aco z
      >>= (apsnd PResults.presults #> (fn rpress => update_result_tail_presults rpress prio z)))
    (empty_action prio)
  in
    (get_presults >>> arr PResults.run_presults) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
    |> PAction.paction
  end

fun paction_from_presults e = gen_paction_from_presults (arr PResults.L.getter)
  (Library.K (arr (PAction.disable_paction e)))

fun gen_update_result_tail_presults update_result update_tail_presults (x, aco) prio =
  update_result prio x >>> update_tail_presults prio aco

(*TODO*)
(* fun update_tail_presults prs = (PResults.L.lens () |> L.set |> curry) prs
  >>> gen_inc_actiona_num (action_actiona_num () |> L.modify) *)
end

end

