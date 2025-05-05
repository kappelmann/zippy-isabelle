(*  Title:      Zippy/zippy_paction_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN =
sig
  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  type @{AllT_args} zipper = @{AllT_args} PACTION.zipper
  type prio = PACTION.prio

  val gen_paction_from_presults :
    (*get presults*)
    (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} PRESULTS.presults) cat ->
    (*action when results are empty*)
    @{AllT_args} PACTION.action ->
    (*update zipper with pulled result and the remaining presults*)
    (PRESULTS.result * @{AllT_args} PRESULTS.presults -> @{AllT_args} PACTION.action) ->
    @{AllT_args} PACTION.paction

  val paction_from_presults : @{ParaT_args encl = "(" ")"} PRESULTS.CO.AE.exn ->
    (PRESULTS.result * @{AllT_args} PRESULTS.presults -> @{AllT_args} PACTION.action) ->
    @{AllT_args} PACTION.paction

  val gen_update_result_tail_presults :
    (*update with pulled result*)
    (prio -> PRESULTS.result -> (@{ParaT_args} @{AllT_args} zipper, 'z) cat) ->
    (*update with remaining presults*)
    (prio -> @{AllT_args} PRESULTS.presults -> (@{ParaT_args} 'z, @{AllT_args} zipper) cat) ->
    PRESULTS.result * @{AllT_args} PRESULTS.presults -> @{AllT_args} PACTION.action

  (* val update_tail_presults : @{AllT_args} PRESULTS.presults ->
    (@{ParaT_args} @{AllT_args} zipper) hom_move *)
end

functor Zippy_PAction_Presults_Mixin(
    PACTION_PRESULTS : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PACTION_PRESULTS_MIXIN =
struct

open PACTION_PRESULTS
structure U = Zippy_Monad_Util(PACTION.L.K.M); open U
structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(PACTION.L.K.M); open M
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  open PRESULTS.CO.AE; structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli"\<close>(M))
structure PACTION = Zippy_PAction_Mixin(open PACTION_PRESULTS; structure AE = AE)

type @{AllT_args} zipper = @{AllT_args} PACTION.zipper
type prio = PACTION.prio

local open SC MO A
in
fun gen_paction_from_presults get_presults empty_action update_result_tail_presults =
  let fun update_action rp_aco prio = AE.catch'
    (fn z => PRESULTS.CO.resume rp_aco z
      >>= (apsnd PRESULTS.presults #> (fn rpress => update_result_tail_presults rpress prio z)))
    (empty_action prio)
  in
    (get_presults >>> arr (PRESULTS.dest_presults #> PRESULTS.CO.resume)) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
    |> PACTION.paction
  end

fun paction_from_presults e = gen_paction_from_presults PRESULTS.L.getter
  (Library.K (PACTION.disable_paction e))

fun gen_update_result_tail_presults update_result update_tail_presults (x, aco) prio =
  update_result prio x >>> update_tail_presults prio aco

(*TODO*)
(* fun update_tail_presults prs = (PRESULTS.L.lens () |> L.set |> curry) prs
  >>> gen_inc_actiona_num (action_actiona_num () |> L.modify) *)
end

end

