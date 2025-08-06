(*  Title:      Zippy/zippy_instance_resolve.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_RESOLVE =
sig
  include ZIPPY_INSTANCE_TAC

  structure Resolve :
  sig
    (*resolution with single theorem*)
    type @{AllT_args} data = {
      empty_action : @{AllT_args} Base_Data.PAction.action,
      thm : thm,
      updates : (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph) list,
      mk_cud : @{AllT_args} Result_Action.mk_copy_update_data,
      progress : Base_Data.AAMeta.P.progress,
      prio_sq_co : @{AllT_args} PResults.prio_sq_co}

    val eq_data : @{AllT_args} data * @{AllT_args} data -> bool
    val pretty_data : Proof.context -> @{AllT_args} data -> Pretty.T

    val tac_data_from_data : Base_Data.AMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> Proof.context -> Base_Data.GFocus.focus ->
        Tac_AAM.ztactic) ->
      @{AllT_args} data -> @{AllT_args} Tac.data

    val paction_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      Base_Data.AMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> Proof.context -> Base_Data.GFocus.focus ->
        Tac_AAM.ztactic) ->
      @{AllT_args} data -> @{AllT_args} PAction.data

    val cons_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.AMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> Proof.context -> Base_Data.GFocus.focus ->
        Tac_AAM.ztactic) ->
      @{AllT_args} data -> Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLP.Z3.zipper,
        @{AllT_args} ZLP.Z4.zipper) morph

    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> Proof.context -> Base_Data.GFocus.focus ->
        Tac_AAM.ztactic) ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph

    val cons_resolve_ho_unif_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph
    val cons_resolve_ho_match_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph

    val cons_eresolve_ho_unif_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph
    val cons_eresolve_ho_match_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph

    val cons_dresolve_ho_unif_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph
    val cons_dresolve_ho_match_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph

    val cons_fresolve_ho_unif_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph
    val cons_fresolve_ho_match_first_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph
  end
end

functor Zippy_Instance_Resolve (
    structure Z : ZIPPY_INSTANCE_TAC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INSTANCE_RESOLVE =
struct
open Z; open ZLP MU

structure Resolve =
struct
local open Base_Data
in
type @{AllT_args} data = {
  empty_action : @{AllT_args} PAction.action,
  thm : thm,
  updates : (GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph) list,
  mk_cud : @{AllT_args} Result_Action.mk_copy_update_data,
  progress : AAMeta.P.progress,
  prio_sq_co : @{AllT_args} PResults.prio_sq_co}
end

fun eq_data ({thm = thm1, progress = progress1,...},
  {thm = thm2, progress = progress2,...}) =
  Thm.eq_thm (thm1, thm2) andalso progress1 = progress2

fun pretty_data ctxt {thm, progress,...} =
  SpecCheck_Show.record [
    ("thm", Thm.pretty_thm ctxt thm),
    ("progress", Mixin5.Meta.Meta.P.pretty progress)
  ]

local open SC A
in
fun tac_data_from_data meta resolve_tac
  {empty_action, thm, updates, mk_cud, progress, prio_sq_co} = {
  meta = meta, empty_action = empty_action,
  result_action = Result_Action.hom_changed_goals_action updates mk_cud,
  prio_sq_co = prio_sq_co,
  tac = Ctxt.with_ctxt (resolve_tac progress thm #> arr)}

fun paction_data_from_data exn meta resolve_tac = tac_data_from_data meta resolve_tac
  #> Tac.paction_data_from_data exn

fun cons_action exn meta resolve_tac = paction_data_from_data exn meta resolve_tac
  #> Z.PAction.cons_action

fun cons_action_cluster exn meta resolve_tac data = Ctxt.with_ctxt (fn ctxt => data
  |> map_index (Library.uncurry (fn i => apsnd (fn (data as {thm, ...}) => fn focus =>
    let val meta = Base_Data.AMeta.metadata (
      Zippy_Identifier.suffix_name NONE (string_of_int i) (Base_Data.ACMeta.Id.getter meta),
      Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str (Base_Data.ACMeta.Descr.getter meta |> Lazy.force),
        Pretty.block [Pretty.str "Theorem: ", Thm.pretty_thm ctxt thm]
      ] |> Pretty.block |> Pretty.string_of))
    in cons_action exn meta resolve_tac data focus >>> Up4.morph end)))
  |> Node.cons3 exn meta)
end

fun cons_resolve_ho_unif_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding resolve_ho_unif_first},
    Lazy.value "Resolution with higher-order unification on first possible goal."))
  Tac_AAM.resolve_ho_unif_first_ztac
fun cons_resolve_ho_match_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding resolve_ho_match_first},
    Lazy.value "Resolution with higher-order matching on first possible goal."))
  Tac_AAM.resolve_ho_match_first_ztac

fun cons_eresolve_ho_unif_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding eresolve_ho_unif_first},
    Lazy.value "E-resolution with higher-order unification on first possible goal."))
  Tac_AAM.eresolve_ho_unif_first_ztac
fun cons_eresolve_ho_match_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding eresolve_ho_match_first},
    Lazy.value "E-resolution with higher-order matching on first possible goal."))
  Tac_AAM.eresolve_ho_match_first_ztac

fun cons_dresolve_ho_unif_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding dresolve_ho_unif_first},
    Lazy.value "D-resolution with higher-order unification on first possible goal."))
  Tac_AAM.dresolve_ho_unif_first_ztac
fun cons_dresolve_ho_match_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding dresolve_ho_match_first},
    Lazy.value "D-resolution with higher-order matching on first possible goal."))
  Tac_AAM.dresolve_ho_match_first_ztac

fun cons_fresolve_ho_unif_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding fresolve_ho_unif_first},
    Lazy.value "F-resolution with higher-order unification on first possible goal."))
  Tac_AAM.fresolve_ho_unif_first_ztac
fun cons_fresolve_ho_match_first_action_cluster exn = cons_action_cluster exn
  (Base_Data.ACMeta.metadata (@{binding fresolve_ho_match_first},
    Lazy.value "F-resolution with higher-order matching on first possible goal."))
  Tac_AAM.fresolve_ho_match_first_ztac
end
end
