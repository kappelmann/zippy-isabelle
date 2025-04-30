(*  Title:      Zippy/zippy_paction_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN =
sig
  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = M.t
  sharing type AE.exn = PRESULTS.CO.AE.exn

  val gen_paction_from_presults :
    (*get presults*)
    (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} PRESULTS.presults) cat ->
    (*action when results are empty*)
    @{AllT_args} PACTION.action ->
    (*update zipper with pulled result and the remaining presults*)
    (PRESULTS.result * @{AllT_args} PRESULTS.presults -> @{AllT_args} PACTION.action) ->
    @{AllT_args} PACTION.paction

  val paction_from_presults : @{ParaT_args encl = "(" ")"} AE.exn ->
    (PRESULTS.result * @{AllT_args} PRESULTS.presults -> @{AllT_args} PACTION.action) ->
    @{AllT_args} PACTION.paction

  val gen_update_result_tail_presults :
    (*update with pulled result*)
    (prio -> PRESULTS.result -> (@{ParaT_args} @{AllT_args} zipper, 'z) cat) ->
    (*update with remaining presults*)
    (prio -> @{AllT_args} PRESULTS.presults -> (@{ParaT_args} 'z, @{AllT_args} zipper) cat) ->
    PRESULTS.result * @{AllT_args} PRESULTS.presults -> @{AllT_args} PACTION.action

  val gen_update_result :
    (*init child node*)
    (prio -> 'res -> (@{ParaT_args} @{AllT_args} zipper, 'cud * 'ch) cat) ->
    (*update child node*)
    ('cud -> (@{ParaT_args} 'ch, 'z) cat) ->
    prio -> 'res -> (@{ParaT_args} @{AllT_args} zipper, 'z) cat

  val gen_update_result_copy_parent_actions :
    (*init child node*)
    (prio -> 'res -> (@{ParaT_args} @{AllT_args} zipper, 'cud * 'ch) cat) ->
    (*get parent actions*)
    (@{ParaT_args} 'ch, 'pas) cat ->
    (*copy parent actions*)
    ('cud -> 'pas -> (@{ParaT_args} 'ch, 'z) cat) ->
    (*update child node*)
    ('cud -> (@{ParaT_args} 'z) hom_move) ->
    prio -> 'res -> (@{ParaT_args} @{AllT_args} zipper, 'z) cat

  (* val update_tail_presults : @{AllT_args} PRESULTS.presults ->
    (@{ParaT_args} @{AllT_args} zipper) hom_move *)
end

functor Zippy_PAction_Presults_Mixin(
    structure Z : ZIPPY_BASE
    structure PACTION_PRESULTS : ZIPPY_PACTION_PRESULTS_MIXIN_BASE
    sharing type PACTION_PRESULTS.zipper = Z.Z4.zipper
    sharing type PACTION_PRESULTS.M.t = Z.M.t
    sharing type PACTION_PRESULTS.PACTION.L.lens = Z.L.lens
    sharing type PACTION_PRESULTS.PRESULTS.CO.acoroutine = Z.CO.acoroutine
    sharing type PACTION_PRESULTS.PRESULTS.CO.AE.exn = Z.CO.AE.exn
  ) : ZIPPY_PACTION_PRESULTS_MIXIN =
struct

open Z PACTION_PRESULTS
structure PACTION = Zippy_PAction_Mixin(structure Z = Z; open PACTION_PRESULTS)

local open SC MO A
in
fun gen_paction_from_presults get_presults empty_action update_result_tail_presults =
  let fun update_action rp_aco prio = AE.catch'
    (fn z => CO.resume rp_aco z
      >>= (apsnd PRESULTS.presults #> (fn rpress => update_result_tail_presults rpress prio z)))
    (empty_action prio)
  in
    (get_presults >>> arr (PRESULTS.dest_presults #> CO.resume)) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
    |> PACTION.paction
  end

fun paction_from_presults e = gen_paction_from_presults PRESULTS.L.getter
  (Library.K (PACTION.disable_paction e))

fun gen_update_result_tail_presults update_result update_tail_presults (x, aco) prio =
  update_result prio x >>> update_tail_presults prio aco

fun gen_update_result init_child update_child prio x = init_child prio x >>> uncurry update_child

fun gen_update_result_copy_parent_actions init_child get_parent_actions copy_parent_actions
  update_child =
  gen_update_result init_child
  (fn cud => fn z =>
    get_parent_actions z >>= (fn pas => copy_parent_actions cud pas z) >>= update_child cud)

(*TODO*)
(* fun update_tail_presults prs = (PRESULTS.L.lens () |> L.set |> curry) prs
  >>> gen_inc_actiona_num (action_actiona_num () |> L.modify) *)
end

end

