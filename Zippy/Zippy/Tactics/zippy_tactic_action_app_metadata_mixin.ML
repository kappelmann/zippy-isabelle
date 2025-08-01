(*  Title:      Zippy/zippy_tactic_action_app_metadata_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN =
sig
  include ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN_BASE

  type rtactic = Meta.Meta.metadata Tac.RTac.rtactic
  type ztactic = Meta.Meta.metadata Tac.ztactic

  (* liftings *)
  val madd : Meta.Meta.metadata * Meta.Meta.metadata -> Meta.Meta.metadata
  val lift_tac_progress : Meta.Meta.P.progress -> (int -> tactic) -> int -> ztactic

  (* concrete tactics *)
  val all_ztac : Meta.Meta.P.progress -> ztactic

  val assume_ho_unif_ztac : Proof.context -> Tac.GPU.F.focus -> ztactic

  val resolve_ho_unif_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val resolve_ho_unif_first_ztac : Meta.Meta.progress -> thm -> Proof.context -> Tac.GPU.F.focus ->
    ztactic
  val resolve_ho_match_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val resolve_ho_match_first_ztac : Meta.Meta.progress -> thm -> Proof.context ->
    Tac.GPU.F.focus -> ztactic

  val eresolve_ho_unif_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val eresolve_ho_unif_first_ztac : Meta.Meta.progress -> thm -> Proof.context -> Tac.GPU.F.focus ->
    ztactic
  val eresolve_ho_match_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val eresolve_ho_match_first_ztac : Meta.Meta.progress -> thm -> Proof.context ->
    Tac.GPU.F.focus -> ztactic

  val dresolve_ho_unif_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val dresolve_ho_unif_first_ztac : Meta.Meta.progress -> thm -> Proof.context -> Tac.GPU.F.focus ->
    ztactic
  val dresolve_ho_match_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val dresolve_ho_match_first_ztac : Meta.Meta.progress -> thm -> Proof.context ->
    Tac.GPU.F.focus -> ztactic

  val fresolve_ho_unif_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val fresolve_ho_unif_first_ztac : Meta.Meta.progress -> thm -> Proof.context -> Tac.GPU.F.focus ->
    ztactic
  val fresolve_ho_match_any_first_ztac : Meta.Meta.progress -> thm list -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
  val fresolve_ho_match_first_ztac : Meta.Meta.progress -> thm -> Proof.context ->
    Tac.GPU.F.focus -> ztactic
end

functor Zippy_Tactic_Action_App_Metadata_Mixin(
    Tac_AAM : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN_BASE
  ) : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN =
struct
open Tac_AAM

local structure Meta = Meta.Meta
in
type rtactic = Meta.metadata Tac.RTac.rtactic
type ztactic = Meta.metadata Tac.ztactic

(* liftings *)
val madd = Meta.add

fun lift_tac_progress progress = Tac.RTac.lift_tac' (Library.K (Meta.metadata progress))
  #> Tac.lift_rtac_single_goal

(* concrete tactics *)
fun all_ztac progress = Tac.all_ztac (Meta.metadata progress)

fun gen_assume_ztac assume_tac ctxt = assume_tac ctxt
  |> lift_tac_progress Meta.P.promising
  |> Tac.ZFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
fun assume_ho_unif_ztac ctxt = gen_assume_ztac assume_tac ctxt

(** resolution **)
fun gen_resolve_ho_unif_first_ztac resolve_tac progress thms = resolve_tac thms
  #> lift_tac_progress progress
  #> Tac.ZFIRST_GOAL_FOCUS_NONE_FIRST_GOAL

val resolve_ho_unif_any_first_ztac = gen_resolve_ho_unif_first_ztac (General_Util.flip resolve_tac)
fun resolve_ho_unif_first_ztac progress = single #> resolve_ho_unif_any_first_ztac progress
val resolve_ho_match_any_first_ztac = gen_resolve_ho_unif_first_ztac (General_Util.flip match_tac)
fun resolve_ho_match_first_ztac progress = single #> resolve_ho_match_any_first_ztac progress

val eresolve_ho_unif_any_first_ztac = gen_resolve_ho_unif_first_ztac (General_Util.flip eresolve_tac)
fun eresolve_ho_unif_first_ztac progress = single #> eresolve_ho_unif_any_first_ztac progress
val eresolve_ho_match_any_first_ztac = gen_resolve_ho_unif_first_ztac (General_Util.flip ematch_tac)
fun eresolve_ho_match_first_ztac progress = single #> eresolve_ho_match_any_first_ztac progress

local
  fun gen_dresolve_ztac elim_tac =
    let
      (*Tactic.make_elim allows no context passing but Thm.biresolution fails to certificate certain
      theorems without a context*)
      fun make_elim ctxt thm =
        let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
        in zero_var_indexes (resolve revcut_rl) end
      fun tac thms ctxt = elim_tac ctxt (List.map (make_elim ctxt) thms)
    in gen_resolve_ho_unif_first_ztac tac end
in
val dresolve_ho_unif_any_first_ztac = gen_dresolve_ztac eresolve_tac
fun dresolve_ho_unif_first_ztac progress = single #> dresolve_ho_unif_any_first_ztac progress
val dresolve_ho_match_any_first_ztac = gen_dresolve_ztac ematch_tac
fun dresolve_ho_match_first_ztac progress = single #> dresolve_ho_match_any_first_ztac progress
end

val fresolve_ho_unif_any_first_ztac = gen_resolve_ho_unif_first_ztac (General_Util.flip forward_tac)
fun fresolve_ho_unif_first_ztac progress = single #> fresolve_ho_unif_any_first_ztac progress
local structure HOPU = Higher_Order_Pattern_Unification
in
val fmatch_tac = Unify_Resolve_Base.unify_fresolve_any_tac HOPU.norms_match HOPU.match
end
val fresolve_ho_match_any_first_ztac = gen_resolve_ho_unif_first_ztac fmatch_tac
fun fresolve_ho_match_first_ztac progress = single #> fresolve_ho_match_any_first_ztac progress

end
end
