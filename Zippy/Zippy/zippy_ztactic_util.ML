(*  Title:      Zippy/zippy_ztactic_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ZTACTIC_UTIL =
sig
  type ztactic = Zippy.Mixin5.Meta.Meta.metadata Zippy.Tac.ztactic

  (* misc *)
  val ztactic_resultsq : ztactic -> @{AllT_args} Zippy.Z2.zipper ->
    Zippy.Mixin4.PResults.result Seq.seq

  (* priorities *)
  val with_halve_prio_depth_res_co :
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper * Zippy.Mixin4.PResults.result Seq.seq,
      Zippy.Prio.prio * Zippy.Mixin4.PResults.result Seq.seq) Zippy.Co.Co.coroutine ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper * Zippy.Mixin4.PResults.result Seq.seq,
      Zippy.Prio.prio * Zippy.Mixin4.PResults.result Seq.seq) Zippy.Co.Co.coroutine
  (*halves the priorities with each pull of a result*)
  val enum_halve_prio_depth_res_co : (@{ParaT_args} Zippy.Prio.prio) Zippy.emorph ->
    Zippy.Prio.prio ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper * Zippy.Mixin4.PResults.result Seq.seq,
      Zippy.Prio.prio * Zippy.Mixin4.PResults.result Seq.seq) Zippy.Co.Co.coroutine
  val halve_prio_halve_prio_depth_res_co : Zippy.Prio.prio ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper * Zippy.Mixin4.PResults.result Seq.seq,
      Zippy.Prio.prio * Zippy.Mixin4.PResults.result Seq.seq) Zippy.Co.Co.coroutine

  (* action *)
  val cons_ztactic_action :
    (Zippy.Mixin4.PResults.result * @{AllT_args} Zippy.Mixin4.PResults.presults ->
       @{AllT_args} Zippy.Mixin4.PAction.action) ->
    Zippy.Mixin4.Meta.Meta.metadata ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper * Zippy.Mixin4.PResults.result Seq.seq,
      Zippy.Mixin4.PResults.prio * Zippy.Mixin4.PResults.result Seq.seq) Zippy.Co.Co.coroutine ->
    (@{ParaT_args} Zippy.Tac.GPU.F.focus, ztactic) Zippy.morph -> Zippy.Tac.GPU.F.focus ->
    (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.morph

  (* action cluster *)
  val cons_single_ztactic_action_cluster :
    Zippy.Mixin3.Meta.Meta.metadata ->
    (Zippy.Mixin4.PResults.result * @{AllT_args} Zippy.Mixin4.PResults.presults ->
       @{AllT_args} Zippy.Mixin4.PAction.action) ->
    Zippy.Mixin4.Meta.Meta.metadata ->
    (@{ParaT_args} @{AllT_args} Zippy.Z4.zipper * Zippy.Mixin4.PResults.result Seq.seq,
      Zippy.Mixin4.PResults.prio * Zippy.Mixin4.PResults.result Seq.seq) Zippy.Co.Co.coroutine ->
    (@{ParaT_args} Zippy.Tac.GPU.F.focus, ztactic) Zippy.morph -> Zippy.Tac.GPU.F.focus ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  (* concrete tactics *)
  (*solves every goal*)
  val cheat_tac : Proof.context -> Zippy.Tac.GPU.F.focus -> ztactic

  (*resolution with theorems*)
  val resolve_moved_tac : Zippy_Action_App_Progress.progress -> thm list ->
    Proof.context -> Zippy.Tac.GPU.F.focus -> ztactic
end

structure Zippy_ZTactic_Util : ZIPPY_ZTACTIC_UTIL =
struct
open Zippy Zippy.MU

type ztactic = Mixin5.Meta.Meta.metadata Tac.ztactic

(* misc *)
fun ztactic_resultsq tac z2 = tac (Mixin2.GCluster.get_state z2)

(* priorities *)
local open SC Mo A
in
fun with_halve_prio_depth_res_co x =
  Mixin4.PResults_Pos.with_depth_prio_res_co (fn i => arr (funpow i Prio.halve)) x

(* fun halve_prio_co p = Mixin4.PResults.enum_prio_res_co (arr Prio.halve) p *)
fun enum_halve_prio_depth_res_co next p = Mixin4.PResults.enum_prio_res_co next p
  |> with_halve_prio_depth_res_co
fun halve_prio_halve_prio_depth_res_co x = enum_halve_prio_depth_res_co (arr Prio.halve) x

(* action *)
fun cons_ztactic_action result_tail_presults_action meta mk_prio_sq_c tac focus z3 = Up3.morph z3
  >>= (fn z2 => tac focus
  >>= (fn tac =>
    let val presults = ztactic_resultsq tac z2 |> Mixin4.PResults.presults_from_sq exn mk_prio_sq_c
    in Util.cons_presults_action result_tail_presults_action meta focus presults z3 end))

(* action cluster *)
fun cons_single_ztactic_action_cluster actionc_meta result_tail_presults_action action_meta
  mk_prio_sq_c tac focus =
  let val add_action = cons_ztactic_action result_tail_presults_action action_meta mk_prio_sq_c tac
  in Util.cons_action_cluster actionc_meta [(focus, add_action)] end

local structure Meta = Mixin5.Meta.Meta
in
fun cheat_tac ctxt = Skip_Proof.cheat_tac ctxt
  |> Tac.RTac.lift_tac' (Library.K (Meta.metadata Zippy_Action_App_Progress.promising))
  |> Tac.lift_all_goals_focus_tac Tac.no_tac Meta.add Tac.single_goal_empty_target

fun resolve_moved_tac progress thms ctxt = resolve_tac ctxt thms
  |> Tac.RTac.lift_tac' (Library.K (Meta.metadata progress))
  |> Tac.lift_every_focus_tac Tac.no_tac Meta.add Tac.single_goal_moved_target
end
end

end
