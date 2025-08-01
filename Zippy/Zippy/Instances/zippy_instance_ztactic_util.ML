(*  Title:      Zippy/zippy_instance_ztactic_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_ZTACTIC_UTIL =
sig
  (* misc *)
  val ztactic_resultsq : Zippy.Tac_AAM.ztactic -> @{AllT_args} Zippy.Z2.zipper ->
    Zippy.Mixin4.PResults.result Seq.seq

  (* priorities *)
  val enum_halve_prio_sq_co : Zippy.Prio.prio -> @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co
  val with_halve_prio_depth_sq_co : @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co ->
    @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co
  (*halves the priorities with each pull of a result*)
  val enum_halve_prio_depth_sq_co : (@{ParaT_args} Zippy.Prio.prio) Zippy.emorph ->
    Zippy.Prio.prio -> @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co
  val enum_halve_prio_halve_prio_depth_sq_co : Zippy.Prio.prio ->
    @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co

  (* action *)
  type @{AllT_args} ztactic_action_data = {
    meta : Zippy.Mixin4.Meta.Meta.metadata,
    result_tail_presults_action :
      @{AllT_args} Zippy.Mixin4.PAction_PResults.result_tail_presults_action,
    prio_sq_co : @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co,
    tac : (@{ParaT_args} Zippy.Tac.GPU.F.focus, Zippy.Tac_AAM.ztactic) Zippy.morph}

  val cons_ztactic_action : @{AllT_args} ztactic_action_data -> Zippy.Tac.GPU.F.focus ->
    (@{ParaT_args} @{AllT_args} Zippy.Z3.zipper, @{AllT_args} Zippy.Z4.zipper) Zippy.morph

  (* action cluster *)
  val cons_ztactics_action_cluster : Zippy.Mixin3.Meta.Meta.metadata ->
    (Zippy.Tac.GPU.F.focus * @{AllT_args} ztactic_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  (* concrete tactics *)
  (*solves every goal*)
  val cheat_ztac : Proof.context -> Zippy.Tac.GPU.F.focus -> Zippy.Tac_AAM.ztactic

  (*resolution with theorem*)
  type @{AllT_args} resolve_action_data = {
    thm : thm,
    updates : (Zippy.Tac.GPU.GCS.goal_pos ->
      (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper) Zippy.emorph) list,
    mk_cud : @{AllT_args} Zippy.Util.mk_copy_update_data,
    progress : Zippy.Mixin5.Meta.Meta.P.progress,
    prio_sq_co : @{AllT_args} Zippy.Mixin4.PResults.prio_sq_co}

  val eq_resolve_action_data :
    @{AllT_args} resolve_action_data * @{AllT_args} resolve_action_data -> bool
  val pretty_resolve_action_data : Proof.context -> @{AllT_args} resolve_action_data -> Pretty.T

  val cons_resolve_action_cluster :
    (Zippy_Action_App_Progress.progress -> thm -> Proof.context -> Zippy.Tac.GPU.F.focus ->
      Zippy.Tac_AAM.ztactic) ->
    Zippy.Mixin3.Meta.Meta.metadata ->
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  val cons_resolve_ho_unif_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph
  val cons_resolve_ho_match_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  val cons_eresolve_ho_unif_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph
  val cons_eresolve_ho_match_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  val cons_dresolve_ho_unif_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph
  val cons_dresolve_ho_match_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph

  val cons_fresolve_ho_unif_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph
  val cons_fresolve_ho_match_first_action_cluster :
    (Zippy.Tac.GPU.F.focus * @{AllT_args} resolve_action_data) list ->
    (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper, @{AllT_args} Zippy.Z3.zipper) Zippy.morph
end

structure Zippy_Instance_ZTactic_Util : ZIPPY_INSTANCE_ZTACTIC_UTIL =
struct
structure PExn = Exn
open Zippy Zippy.MU

(* misc *)
fun ztactic_resultsq tac z2 = tac (Mixin2.GCluster.get_state z2)

(* priorities *)
local open SC Mo A
in
fun enum_halve_prio_sq_co x = Mixin4.PResults.enum_prio_sq_co (arr Prio.halve) x
fun with_halve_prio_depth_sq_co x =
  Mixin4.PResults_Pos.with_depth_prio_sq_co (fn i => arr (funpow i Prio.halve)) x
fun enum_halve_prio_depth_sq_co next = Mixin4.PResults.enum_prio_sq_co next
  #> with_halve_prio_depth_sq_co
fun enum_halve_prio_halve_prio_depth_sq_co x = enum_halve_prio_depth_sq_co (arr Prio.halve) x

type @{AllT_args} ztactic_action_data = {
  meta : Mixin4.Meta.Meta.metadata,
  result_tail_presults_action : @{AllT_args} Mixin4.PAction_PResults.result_tail_presults_action,
  prio_sq_co : @{AllT_args} Mixin4.PResults.prio_sq_co,
  tac : (@{ParaT_args} Tac.GPU.F.focus, Tac_AAM.ztactic) morph}

(* action *)
fun cons_ztactic_action {meta, result_tail_presults_action, prio_sq_co, tac} focus z3 = Up3.morph z3
  >>= (fn z2 => tac focus
  >>= (fn tac =>
    let val presults = ztactic_resultsq tac z2 |> Mixin4.PResults.presults_from_sq exn prio_sq_co
    in Util.cons_presults_action result_tail_presults_action meta focus presults z3 end))

(* action cluster *)
fun cons_ztactics_action_cluster meta =
  List.map (apsnd (fn data => fn x => cons_ztactic_action data x >>> Up4.morph))
  #> Util.cons_action_cluster meta

fun cheat_ztac ctxt = Tac_AAM.lift_tac_progress Mixin5.Meta.Meta.P.promising (Skip_Proof.cheat_tac ctxt)
  |> Tac.zEVERY_FOCUS_NONE_ALL_GOALS Tac.no_ztac Tac.no_ztac Tac_AAM.madd

(*resolution with theorem*)
type @{AllT_args} resolve_action_data = {
  thm : thm,
  updates : (Tac.GPU.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph) list,
  mk_cud : @{AllT_args} Util.mk_copy_update_data,
  progress : Mixin5.Meta.Meta.P.progress,
  prio_sq_co : @{AllT_args} Mixin4.PResults.prio_sq_co}

fun eq_resolve_action_data ({thm = thm1, progress = progress1,...},
  {thm = thm2, progress = progress2,...}) =
  Thm.eq_thm (thm1, thm2) andalso progress1 = progress2

fun pretty_resolve_action_data ctxt {thm, progress,...} =
  SpecCheck_Show.record [
    ("thm", Thm.pretty_thm ctxt thm),
    ("progress", Mixin5.Meta.Meta.P.pretty progress)
  ]

fun cons_resolve_action_cluster resolve_tac meta data =
  Ctxt.with_ctxt (fn ctxt => data
    |> map_index (Library.uncurry (fn i => apsnd (fn {thm, updates, mk_cud, progress, prio_sq_co} =>
      {meta = Mixin4.Meta.Meta.metadata (
        Zippy_Identifier.suffix_name NONE (string_of_int i) (Mixin3.Meta.Meta.Id.getter meta),
        Lazy.lazy (fn _ => Pretty.breaks [
          Pretty.str (Mixin3.Meta.Meta.Descr.getter meta |> Lazy.force),
          Pretty.block [Pretty.str "Theorem: ", Thm.pretty_thm ctxt thm]
        ] |> Pretty.block |> Pretty.string_of)),
      result_tail_presults_action = Util.result_tail_presults_action
        (Util.hom_changed_goals_update_result updates mk_cud),
      prio_sq_co = prio_sq_co,
      tac = Ctxt.with_ctxt (resolve_tac progress thm #> arr)})))
    |> cons_ztactics_action_cluster meta)

fun cons_resolve_ho_unif_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.resolve_ho_unif_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding resolve_ho_unif_first},
    Lazy.value "Resolution with higher-order unification on first possible goal.")) x
fun cons_resolve_ho_match_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.resolve_ho_match_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding resolve_ho_match_first},
    Lazy.value "Resolution with higher-order matching on first possible goal.")) x

fun cons_eresolve_ho_unif_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.eresolve_ho_unif_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding eresolve_ho_unif_first},
    Lazy.value "E-resolution with higher-order unification on first possible goal.")) x
fun cons_eresolve_ho_match_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.eresolve_ho_match_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding eresolve_ho_match_first},
    Lazy.value "E-resolution with higher-order matching on first possible goal.")) x

fun cons_dresolve_ho_unif_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.dresolve_ho_unif_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding dresolve_ho_unif_first},
    Lazy.value "D-resolution with higher-order unification on first possible goal.")) x
fun cons_dresolve_ho_match_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.dresolve_ho_match_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding dresolve_ho_match_first},
    Lazy.value "D-resolution with higher-order matching on first possible goal.")) x

fun cons_fresolve_ho_unif_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.fresolve_ho_unif_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding fresolve_ho_unif_first},
    Lazy.value "F-resolution with higher-order unification on first possible goal.")) x
fun cons_fresolve_ho_match_first_action_cluster x = cons_resolve_action_cluster
  Tac_AAM.fresolve_ho_match_first_ztac
  (Mixin3.Meta.Meta.metadata (@{binding fresolve_ho_match_first},
    Lazy.value "F-resolution with higher-order matching on first possible goal.")) x
end
end
