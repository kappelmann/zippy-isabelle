\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Auto
  imports
    Context_Parsers
    Zippy_Instance_Resolve
    Zippy_Instance_Simp
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_auto.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

text \<open>Setup the standard instance called \<open>zippy\<close>.\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: Zippy_Auto
  functor_name: Zippy_Instance_Auto
  id: \<open>"zippy"\<close>
  more_args: \<open>
    structure Z = Zippy
    open Z
    structure TI = Discrimination_Tree
    val resolve_init_args = {
      empty_action = SOME (Library.K (PResults.empty_action Util.exn)),
      default_update = NONE,
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      prio_sq_co = SOME (PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.MEDIUM),
      progress = SOME Base_Data.AAMeta.P.Unclear,
      del_select = SOME (Library.K true)}\<close>\<close>
\<close>
local_setup\<open>Zippy_Auto.Init_Goal_Clusters.Data.setup_attribute NONE\<close>

ML\<open>
structure Zippy_Auto =
struct open Zippy_Auto

(* parsers *)
\<^functor_instance>\<open>struct_name: Context_Parsers
  functor_name: Context_Parsers
  id: \<open>FI.prefix_id "parse"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Logging.logger
    val parsers_separator = "where"\<close>\<close>

(* add instance specific utilities *)
structure Run =
struct
local open Zippy; open ZLP MU; open Mo SC
  structure ZB = Zippy_Base(structure Z = ZLP; structure Exn = Exn)
  structure Run = Run_Best_First
in
fun init state = Util.init_thm_state state
  >>= Down1.morph
  >>= Z2.ZM.Unzip.morph
  >>= Init_Goal_Clusters.init_all (Library.K Util.exn) (A.K Base_Data.Tac_Res.GPU.F.none)

fun init_run run ctxt = (init >>> ZB.top2 >>> Z1.ZM.Unzip.morph >>> run)
  #> Run.seq_from_monad {ctxt = ctxt}

fun mk_thmsq get_result_data = Seq.maps get_result_data

fun zippy_tac fuel ctxt =
  let val run = Run.init_repeat_step_queue
    (Ctxt.with_ctxt Run.mk_df_post_unreturned_unfinished_statesq) fuel
  in
    init_run run ctxt
    #> mk_thmsq (Run.get_result_data #> #thm_states)
    (* #> Tactic_Util.unique_thmsq Thm.eq_thm *)
  end
end
end
end
\<close>
local_setup\<open>Zippy_Auto.Context_Parsers.setup_attribute NONE\<close>

paragraph \<open>Resolution\<close>

local_setup\<open>Zippy_Auto.Resolves.Resolve_Unif.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.Resolve_Match.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.EResolve_Unif.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.EResolve_Match.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.DResolve_Unif.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.DResolve_Match.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.FResolve_Unif.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.FResolve_Match.setup_attribute NONE\<close>

declare [[zippy_resolve_unif config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_resolve_match config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_eresolve_unif config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_eresolve_match config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_dresolve_unif config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_dresolve_match config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_fresolve_unif config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]
and [[zippy_fresolve_match config
  default_update: \<open>Zippy.Base_Data.GFocus.single #> Zippy_Auto.Init_Goal_Clusters.init\<close>]]

declare [[zippy_init_gcs \<open>
  let
    open Zippy Zippy_Auto.Resolves.Resolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_resolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> snd #> Data.TI.norm_term #>
      retrieval (Data.get_index (Context.Proof ctxt))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding resolve_ho_unif_first}, cons_ac) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.Resolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_resolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> snd #> Data.TI.norm_term
      #> retrieval (Data.get_index (Context.Proof ctxt))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding resolve_ho_match_first}, cons_ac) end\<close>]]
(*TODO: could be made more efficient: we already know the indices of possibly matching premises when
seraching the term index but do not use that information in the subsequent (d/e)resolution*)
declare [[zippy_init_gcs
  \<open>let
    open Zippy Zippy_Auto.Resolves.EResolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_eresolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding eresolve_ho_unif_first}, cons_ac) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.EResolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_eresolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding eresolve_ho_match_first}, cons_ac) end\<close>]]
declare [[zippy_init_gcs
  \<open>let
    open Zippy Zippy_Auto.Resolves.DResolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_dresolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding dresolve_ho_unif_first}, cons_ac) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.DResolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_dresolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding dresolve_ho_match_first}, cons_ac) end\<close>]]
declare [[zippy_init_gcs
  \<open>let
    open Zippy Zippy_Auto.Resolves.FResolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_fresolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding fresolve_ho_unif_first}, cons_ac) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.FResolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_fresolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun cons_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding fresolve_ho_match_first}, cons_ac) end\<close>]]


paragraph \<open>Simplifier\<close>

ML\<open>
local structure Zippy_Simp = Zippy_Instance_Simp(structure Z = Zippy; structure Ctxt = Z.Ctxt)
in structure Zippy = struct open Zippy Zippy_Simp end end
\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy; open ZLP MU; open SC
    val id = @{binding asm_full_simp}
    val prio_sq_co_safe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH1
    val prio_sq_co_unsafe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH
    val data = Simp.asm_full_simp_data Util.exn id prio_sq_co_safe prio_sq_co_unsafe
    fun init _ focus = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)]
      >>> Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse add: \<open>(@{binding simp}, Simplifier.simp_modifiers |> Method.sections)\<close>
  and default: \<open>@{binding simp}\<close>]]


paragraph \<open>Method\<close>

local_setup \<open>
  let
    val parse_fuel = Parse_Util.option Parse.nat
    val parse = Scan.lift parse_fuel
      --| Zippy_Auto.Context_Parsers.parse
      >> (Method.SIMPLE_METHOD oo Zippy_Auto.Run.zippy_tac)
  in Method.local_setup @{binding zippy} parse "Extensible white-box prover based on Zippy" end\<close>

(* declare reflexive[zippy_resolve_match add mk_cud: Zippy.Result_Action.copy_update_data_empty_changed]

schematic_goal "?x \<equiv> ?x"
  apply (tactic \<open>Zippy_Auto.Run.zippy_tac NONE @{context}\<close>)
  back *)

(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Run_Best_First.Logging.Step.logger Logger.ALL\<close>]] *)
(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Run_Best_First.Logging.Run.logger Logger.ALL\<close>]] *)
(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.ALL\<close>]] *)

(*TODO:
- A^* (1/prio = cost VS (0, 1))
- blast timelimit
*)


(* setup\<open>fn thy =>
  let
    open Zippy_Resolve_Data_Args Zippy
    val context = Context.Theory thy
    val ctxt = Context.proof_of context

    val kind_filters = [
      Bires.intro_bang_kind, Bires.elim_bang_kind, Bires.dest_bang_kind,
      Bires.intro_kind, Bires.elim_kind, Bires.dest_kind]
    val nkinds = length kind_filters
    val [sintro, selim, sdest, intro, elim, dest, _] = Classical.dest_decls ctxt (K true)
      |> partition_list (fn i => fn x =>
          let val kind = snd x |> #kind
          in i = nkinds orelse i = find_index (equal kind) kind_filters end)
        0 nkinds
      |> List.map (List.map fst)

    val args = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates [],
      PAA.progress Base_Data.AAMeta.P.Promising,
      PAA.prio_sq_co (Tac_Util.enum_halve_prio_sq_co Prio.VERY_HIGH)]
    val context = context
      |> fold (Zippy_Auto.Resolve_Match.insert_args_context_defaults args) sintro
      |> fold (Zippy_Auto.EResolve_Match.insert_args_context_defaults args) selim
      |> fold (Zippy_Auto.DResolve_Match.insert_args_context_defaults args) sdest

    val args = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates [],
      PAA.progress Base_Data.AAMeta.P.Promising,
      PAA.prio_sq_co (Tac_Util.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH)]
    val context = context
      |> fold (Zippy_Auto.Resolve_Unif.insert_args_context_defaults args) sintro
      |> fold (Zippy_Auto.EResolve_Unif.insert_args_context_defaults args) selim
      |> fold (Zippy_Auto.DResolve_Unif.insert_args_context_defaults args) sdest

    val args = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates []]
    val context = context
      |> fold (Zippy_Auto.Resolve_Unif.insert_args_context_defaults args) intro
      |> fold (Zippy_Auto.EResolve_Unif.insert_args_context_defaults args) elim
      |> fold (Zippy_Auto.DResolve_Unif.insert_args_context_defaults args) dest
  in Context.theory_of context end
\<close> *)

(* declare [[zippy_init_gcs \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding auto_tac}
    fun tac ctxt = auto_tac ctxt |> CHANGED |> SELECT_GOAL
    fun ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val mk_cud = Result_Action.copy_update_data
    val action_data = {
      empty_action = PResults.empty_action Util.exn,
      meta = Mixin4.Meta.Meta.empty id,
      result_action = Result_Action.action (Library.K (C.id ())) mk_cud,
      prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH,
      tac = Ctxt.with_ctxt (ztac #> arr)
    }
    fun init_ac _ focus =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, action_data)]
      >>> Up3.morph
  in (id, init_ac) end\<close>]] *)

(* declare conjI[zippy_resolve_match_data
  prio_sq_co = \<open>PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.VERY_HIGH\<close>
  and progress = Zippy.Base_Data.AAMeta.P.Promising]
declare TrueI[zippy_resolve_unif_data
  prio_sq_co = \<open>PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.VERY_HIGH\<close>
  and progress = Zippy.Base_Data.AAMeta.P.Promising]
declare disjI1[zippy_resolve_match_data]
declare disjI2[zippy_resolve_match_data]
declare conjE[zippy_eresolve_match_data progress = Zippy.Base_Data.AAMeta.P.Promising] *)



end
