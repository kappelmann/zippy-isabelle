\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Auto
  imports
    Generic_Table_Data
    Zippy_Instance_Resolve
    Main
begin

declare[[ML_print_depth=100]]
(* declare[[ML_map_context \<open>Logger.set_log_levels Logger.root Logger.ALL\<close>]] *)

(*ground polymorphic types since only ground types can be stored in the generic context.*)
setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML\<open>
functor Zippy_Instance_Auto(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_RESOLVE
    where type Base_Data.PAction.prio = Prio.prio (*TODO*)
    val exn : @{ParaT_args encl: "(" ")"} Z.Exn.ME.exn
  ) =
struct
structure FI = Functor_Instance(FI)
structure Logging =
struct
  val logger = Logger.setup_new_logger zippy_base_logger FI.name
  local structure Base = struct val parent_logger = logger end
  in
  structure Resolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve_Unif")
  structure Resolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve_Match")
  structure EResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve_Unif")
  structure EResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve_Match")
  structure DResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve_Unif")
  structure DResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve_Match")
  structure FResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve_Unif")
  structure FResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve_Match")
  end
end

local open Z; open ZLP in
type init_action_cluster = Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph

\<^functor_instance>\<open>struct_name: Init_AC_Data
  functor_name: Generic_Table_Data
  id: \<open>FI.prefix_id "init_ac"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Logging.logger
    type key = Zippy_Identifier.id
    val pretty_key = Zippy_Identifier.pretty
    val ord_key = Zippy_Identifier.ord
    type value = Zippy_Thm_State.state * (term list * term) list -> init_action_cluster
    val pretty_value = K (K (Pretty.str "<init action cluster morphism>"))\<close>\<close>
structure Logging =
struct open Logging
  structure Init_AC_Data : ZIPPY_LOGGER_MIXIN_BASE = Init_AC_Data
end
local val init_args = {
    empty_action = SOME (PResults.empty_action exn),
    default_update = NONE,
    mk_cud = SOME Result_Action.copy_update_data_empty_changed,
    prio_sq_co = SOME (PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.MEDIUM),
    progress = SOME Base_Data.AAMeta.P.Unclear,
    del_select = SOME (Library.K true)
  }
  structure TI = Discrimination_Tree
in
\<^functor_instance>\<open>struct_name: Resolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "resolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    val init_args = init_args
    structure Log = Logging.Resolve_Unif\<close>\<close>
structure Resolve_Unif = Resolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: Resolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "resolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    val init_args = init_args
    structure Log = Logging.Resolve_Match\<close>\<close>
structure Resolve_Match = Resolve_Match.Resolve_Data

\<^functor_instance>\<open>struct_name: EResolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "eresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    val init_args = init_args
    structure Log = Logging.EResolve_Unif\<close>\<close>
structure EResolve_Unif = EResolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: EResolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "eresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    val init_args = init_args
    structure Log = Logging.EResolve_Match\<close>\<close>
structure EResolve_Match = EResolve_Match.Resolve_Data

\<^functor_instance>\<open>struct_name: DResolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "dresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    val init_args = init_args
    structure Log = Logging.DResolve_Unif\<close>\<close>
structure DResolve_Unif = DResolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: DResolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "dresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    val init_args = init_args
    structure Log = Logging.DResolve_Match\<close>\<close>
structure DResolve_Match = DResolve_Match.Resolve_Data

\<^functor_instance>\<open>struct_name: FResolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "fresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    val init_args = init_args
    structure Log = Logging.FResolve_Unif\<close>\<close>
structure FResolve_Unif = FResolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: FResolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "fresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = TI
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    val init_args = init_args
    structure Log = Logging.FResolve_Match\<close>\<close>
structure FResolve_Match = FResolve_Match.Resolve_Data
end
end
end
\<close>
(*reset grounding*)
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: ZAuto
  functor_name: Zippy_Instance_Auto
  id: \<open>"zauto"\<close>
  more_args: \<open>
    structure Z = Zippy
    val exn = Z.Util.exn
  \<close>\<close>
\<close>
local_setup\<open>ZAuto.Init_AC_Data.setup_attribute NONE\<close>
ML\<open>
local
  open Zippy ZAuto; open ZLP MU; open SC Mo A
  structure GCluster = Zippy_Goal_Cluster_Mixin(Mixin2.GCluster)
  structure ZB = Zippy_Base(structure Z = ZLP; structure Exn = Exn)
  structure ZE = Zippy_Enum_Mixin(Zippy_Enum_Mixin_Base(structure Z = ZLP; structure Co = Co))
in
fun init_action_clusters focus z = Ctxt.get_ctxt () >>= (fn ctxt =>
  let
    val state = GCluster.get_state z
    val goals = Thm.prems_of state |> List.map (Term_Util.strip_subgoal #> snd)
    fun init_with_args init = init (state, goals) focus
    val init = Init_AC_Data.get_table (Context.Proof ctxt)
      |> Init_AC_Data.Table.dest
      |> ZB.LF.foldlM (snd #> init_with_args)
  in init z end)
fun init_goal_clusters_action_clusters co = Z2.ZM.Zip.morph co
  >>= Co.Co.repeat_res (id ()) (init_action_clusters Base_Data.GFocus.none >>> arr Co.Co.continue)
    (ZE.DF_Post2.enum_zipper (Library.K Util.exn))
  >>= arr Co.Co.dest_res
end
\<close>

local_setup\<open>ZAuto.Resolve_Unif.setup_attribute NONE\<close>
local_setup\<open>ZAuto.Resolve_Match.setup_attribute NONE\<close>
local_setup\<open>ZAuto.EResolve_Unif.setup_attribute NONE\<close>
local_setup\<open>ZAuto.EResolve_Match.setup_attribute NONE\<close>
local_setup\<open>ZAuto.DResolve_Unif.setup_attribute NONE\<close>
local_setup\<open>ZAuto.DResolve_Match.setup_attribute NONE\<close>
local_setup\<open>ZAuto.FResolve_Unif.setup_attribute NONE\<close>
local_setup\<open>ZAuto.FResolve_Match.setup_attribute NONE\<close>
declare [[zauto_init_ac \<open>
  let
    open Zippy ZAuto.Resolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_resolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding resolve_ho_unif_first}, init_ac) end\<close>
  \<open>let
    open Zippy ZAuto.Resolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_resolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding resolve_ho_match_first}, init_ac) end\<close>]]
(*TODO: could be made more efficient: we already know the indices of possibly matching premises when
seraching the term index but do not use that information in the subsequent (d/e)resolution*)
declare [[zauto_init_ac
  \<open>let
    open Zippy ZAuto.EResolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_eresolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt =
      fst #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding eresolve_ho_unif_first}, init_ac) end\<close>
  \<open>let
    open Zippy ZAuto.EResolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_eresolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt =
      fst #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding eresolve_ho_match_first}, init_ac) end\<close>]]
declare [[zauto_init_ac
  \<open>let
    open Zippy ZAuto.DResolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_dresolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt =
      fst #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding dresolve_ho_unif_first}, init_ac) end\<close>
  \<open>let
    open Zippy ZAuto.DResolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_dresolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt =
      fst #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding dresolve_ho_match_first}, init_ac) end\<close>]]
declare [[zauto_init_ac
  \<open>let
    open Zippy ZAuto.FResolve_Unif; open ZLP MU.SC
    val cons_resolve = Resolve.cons_fresolve_ho_unif_first_action_cluster Util.exn
    val retrieval = Data.TI.unifiables
    fun lookup ctxt =
      fst #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding fresolve_ho_unif_first}, init_ac) end\<close>
  \<open>let
    open Zippy ZAuto.FResolve_Match; open ZLP MU.SC
    val cons_resolve = Resolve.cons_fresolve_ho_match_first_action_cluster Util.exn
    val retrieval = Data.TI.generalisations
    fun lookup ctxt =
      fst #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
        cons_resolve (init_focused_goals_none_all_data (lookup ctxt) goals focus))
      >>> Up3.morph
  in (@{binding fresolve_ho_match_first}, init_ac) end\<close>]]

declare [[zauto_resolve_unif config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_resolve_match config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_eresolve_unif config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_eresolve_match config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_dresolve_unif config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_dresolve_match config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_fresolve_unif config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]
and [[zauto_fresolve_match config:
  default_update = \<open>Zippy.Base_Data.GFocus.single #> init_action_clusters\<close>]]

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
      |> fold (ZAuto.Resolve_Match.insert_args_context_defaults args) sintro
      |> fold (ZAuto.EResolve_Match.insert_args_context_defaults args) selim
      |> fold (ZAuto.DResolve_Match.insert_args_context_defaults args) sdest

    val args = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates [],
      PAA.progress Base_Data.AAMeta.P.Promising,
      PAA.prio_sq_co (Tac_Util.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH)]
    val context = context
      |> fold (ZAuto.Resolve_Unif.insert_args_context_defaults args) sintro
      |> fold (ZAuto.EResolve_Unif.insert_args_context_defaults args) selim
      |> fold (ZAuto.DResolve_Unif.insert_args_context_defaults args) sdest

    val args = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates []]
    val context = context
      |> fold (ZAuto.Resolve_Unif.insert_args_context_defaults args) intro
      |> fold (ZAuto.EResolve_Unif.insert_args_context_defaults args) elim
      |> fold (ZAuto.DResolve_Unif.insert_args_context_defaults args) dest
  in Context.theory_of context end
\<close> *)

declare [[zauto_init_ac \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding classical_slow_step}
    fun safe_tac ctxt = Classical.safe_tac ctxt |> SELECT_GOAL
    fun safe_ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (safe_tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    fun unsafe_tac ctxt =
      Classical.appWrappers ctxt (Classical.inst_step_tac ctxt APPEND' Classical.unsafe_step_tac ctxt)
    fun unsafe_ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.unclear (unsafe_tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val atomize_prems_tac = Object_Logic.atomize_prems_tac
    fun atomize_prems_ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
        (atomize_prems_tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    (*slow step tac + atomize prems tac from classical.ML*)
    fun ztac ctxt = Tactic_Util.ORELSE' (safe_ztac ctxt, Tactic_Util.APPEND' (unsafe_ztac ctxt,
      atomize_prems_ztac ctxt))
    val mk_cud = Result_Action.copy_update_data
    (* val presults = PResults.presults_from_sq exn prio_sq_co *)
    val data = {
      empty_action = PResults.empty_action Util.exn,
      meta = Base_Data.AMeta.empty id,
      result_action = Result_Action.action (Library.K (C.id ())) mk_cud,
      prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH,
      tac = Ctxt.with_ctxt (ztac #> arr)
    }
    fun init_ac _ focus =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)]
      >>> Up3.morph
  in (id, init_ac) end\<close>]]


declare [[zauto_init_ac \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding asm_full_simp}
    fun safe_tac ctxt = safe_asm_full_simp_tac ctxt #> CHANGED
    fun safe_ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (safe_tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    fun unsafe_tac ctxt = asm_full_simp_tac ctxt #> CHANGED
    fun unsafe_ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (unsafe_tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    fun ztac ctxt = Tactic_Util.ORELSE' (safe_ztac ctxt, unsafe_ztac ctxt)
    val mk_cud = Result_Action.copy_update_data
    val action_data = {
      empty_action = PResults.empty_action Util.exn,
      meta = Mixin4.Meta.Meta.metadata (id,
        Lazy.value "safe asm full simp ORELSE unsafe asm full simp"),
      result_action = Result_Action.action (Library.K (C.id ())) mk_cud,
      prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH,
      tac = Ctxt.with_ctxt (ztac #> arr)
    }
    fun init_ac _ focus =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, action_data)]
      >>> Up3.morph
  in (id, init_ac) end\<close>]]
(* declare [[zauto_init_ac \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding auto_tac}
    fun tac ctxt = auto_tac ctxt |> CHANGED |> SELECT_GOAL
    fun ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val mk_cud = Result_Action.copy_update_data
    val action_data = {
      meta = Mixin4.Meta.Meta.empty id,
      result_tail_presults_action = Util.result_tail_presults_action
        (Util.update_result (Library.K (C.id ())) mk_cud),
      prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH,
      tac = Ctxt.with_ctxt (ztac #> arr)
    }
    fun init_ac _ focus =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, action_data)]
      >>> Up3.morph
  in (id, init_ac) end\<close>]] *)
declare [[zauto_init_ac \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding blast}
    (* TODO depth and time limit?*)
    fun tac ctxt = Blast.depth_tac ctxt 4
    fun ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val mk_cud = Result_Action.copy_update_data
    val action_data = {
      empty_action = PResults.empty_action Util.exn,
      meta = Mixin4.Meta.Meta.empty id,
      result_action = Result_Action.action (Library.K (C.id ())) mk_cud,
      prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.MEDIUM,
      tac = Ctxt.with_ctxt (ztac #> arr)
    }
    fun init_ac _ focus =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, action_data)]
      >>> Up3.morph
  in (id, init_ac) end\<close>]]

(* declare conjI[zauto_resolve_match_data
  prio_sq_co = \<open>PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.VERY_HIGH\<close>
  and progress = Zippy.Base_Data.AAMeta.P.Promising]
declare TrueI[zauto_resolve_unif_data
  prio_sq_co = \<open>PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.VERY_HIGH\<close>
  and progress = Zippy.Base_Data.AAMeta.P.Promising]
declare disjI1[zauto_resolve_match_data]
declare disjI2[zauto_resolve_match_data]
declare conjE[zauto_eresolve_match_data progress = Zippy.Base_Data.AAMeta.P.Promising] *)

ML\<open>
local
  open Zippy; open ZLP MU; open Mo SC
  structure ZB = Zippy_Base(structure Z = ZLP; structure Exn = Exn)
  structure Run = Run_Best_First
in
fun zippy_tac fuel ctxt state =
  let
    fun run _ =
      (*initialise the zipper*)
      (Util.init_thm_state state
      (*add actions*)
      >>= Down1.morph
      >>= Z2.ZM.Unzip.morph
      >>= init_goal_clusters_action_clusters
      >>= ZB.top2
      >>= Z1.ZM.Unzip.morph
      (*run best-first-search*)
      >>= Run.init_repeat_step_queue
        (Ctxt.with_ctxt Run.mk_df_post_promising_unreturned_unfinished_statesq) fuel
      )
      |> Run.seq_from_monad {ctxt = ctxt, state = ()}
      |> Seq.map (Run.get_result_data #> #thm_states) |> Seq.flat
      |> Tactic_Util.unique_thmsq
      |> Seq.pull |> Library.K |> Seq.make
      (* |> Seq.list_of |> Seq.of_list *)
    val ressq = Timing.timing run () |> apfst @{print} |> snd
  in ressq end
end
\<close>

(* schematic_goal shows "((\<forall>x. x = x) \<longrightarrow> P) \<Longrightarrow> P" "True \<and> True" "True \<and> True" "\<not>?P \<and> Q \<Longrightarrow> True \<and> False \<or> ?T"
  "rev (rev xs) = xs"
  "map f xs = map g ys ==> length xs = length ys" *)
(* apply auto *)
(* apply blast *)
(* supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.ALL\<close>]] *)
(* supply map_eq_imp_length_eq[intro] *)
lemma choice_eq: "(\<forall>x. \<exists>!y. P x y) = (\<exists>!f. \<forall>x. P x (f x))" (is "?lhs = ?rhs")
supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Run_Best_First.Logging.Step.logger Logger.ALL\<close>]]
supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Run_Best_First.Logging.Run.logger Logger.ALL\<close>]]
proof (intro iffI allI)
  assume L: ?lhs
  then have \<section>: "\<forall>x. P x (THE y. P x y)"
    apply -
    supply theI'[intro]
    (* apply (tactic \<open>zippy_tac NONE @{context}\<close>) *)
done
  show ?rhs
    apply (insert L \<section> )
    (* apply (tactic \<open>zippy_tac NONE @{context}\<close>) *)
    done
next
  fix x
  assume R: ?rhs
  then obtain f where f: "\<forall>x. P x (f x)" and f1: "\<And>y. (\<forall>x. P x (y x)) \<Longrightarrow> y = f"
    by (blast elim: ex1E)
  show "\<exists>!y. P x y"
  proof (rule ex1I)
    show "P x (f x)"
      using f by blast
    show "y = f x" if "P x y" for y
    proof -
      show ?thesis
        using f that f1 [of "\<lambda>z. if z = x then y else f z"]
        (* supply fun_cong[dest] *)
        supply if_split_asm[split]
        supply cong[dest]
        supply [[zauto_init_ac del: \<open>@{binding blast}\<close>]]
        apply -
        apply (tactic \<open>zippy_tac NONE @{context}\<close>)
        done
    qed
  qed
qed

(*TODO:
- A^* (1/prio = cost VS (0, 1))
- separate priorities for tactic combinations
- induction
- blast timelimit
*)


end
