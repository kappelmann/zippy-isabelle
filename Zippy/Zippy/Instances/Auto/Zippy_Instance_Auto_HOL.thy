\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Auto_HOL
  imports
    Cases_Tactics_HOL
    Extended_Blast_Data
    Zippy_Instance_Classical
    Zippy_Instance_Auto_Pure
    Zippy_Instance_Subst
begin

paragraph \<open>Simplifier\<close>

declare [[zippy_parse del: \<open>@{binding simp}\<close>
  and add: \<open>(@{binding simp}, Zippy_Auto.Simp.parse_extended Splitter.split_modifiers)\<close>]]

paragraph \<open>Classical Reasoner\<close>

ML\<open>
local
  structure Base = struct structure Z = Zippy; structure Ctxt = Z.Ctxt end
  structure Zippy_Classical = Zippy_Instance_Classical(open Base)
in
structure Zippy = struct open Zippy Zippy_Classical end
structure Zippy_Auto =
struct open Zippy_Auto
\<^functor_instance>\<open>struct_name: Extended_Blast_Data
  functor_name: Extended_Blast_Data
  id: \<open>FI.prefix_id "blast"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val init_args = {depth = SOME 4, timeout = SOME 7.0}
    val parent_logger = Logging.logger
    \<close>\<close>
end
end
\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy; open ZLP MU; open SC
    val id = @{binding classical_slow_step}
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    val prio_sq_co_safe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.VERY_HIGH
    val prio_sq_co_unsafe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.MEDIUM
    val prio_sq_co_atomize_prems = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH
    val data = Classical.slow_step_atomize_prems_data Util.exn id update mk_cud
      prio_sq_co_safe prio_sq_co_unsafe prio_sq_co_atomize_prems
    fun init _ focus = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)]
      >>> Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_parse add: \<open>(@{binding clasimp}, Clasimp.clasimp_modifiers |> Method.sections)\<close>
  and default: \<open>@{binding clasimp}\<close>]]

local_setup\<open>Zippy_Auto.Extended_Blast_Data.setup_attribute NONE\<close>
declare [[zippy_init_gcs \<open>
  let
    open Zippy Zippy_Auto; open ZLP MU; open SC A
    val id = @{binding blast}
    val prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.LOW
    val tac = Extended_Blast_Data.blast_tac
    val ztac = tac
      #> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      #> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val data = {
      empty_action = Library.K (PResults.empty_action Util.exn),
      meta = Mixin4.Meta.Meta.metadata (id, Lazy.value "blast with depth and timeout limit"),
      result_action = Result_Action.action (Library.K (C.id ())) Result_Action.copy_update_data,
      prio_sq_co = prio_sq_co,
      tac = Ctxt.with_ctxt (ztac #> arr)}
    fun init _ focus = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)]
      >>> Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_parse \<open>(@{binding blast}, Scan.depend (fn context =>
  Zippy_Auto.Extended_Blast_Data.parse_attribute
  >> (fn attr => (ML_Attribute_Util.attribute_map_context attr context, ()))))\<close>]]

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

paragraph \<open>Substitution\<close>

ML\<open>
structure Zippy_Auto =
struct open Zippy_Auto
local open Zippy
in
\<^functor_instance>\<open>struct_name: Subst
  functor_name: Zippy_Instance_Subst_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Zippy
    structure TI = Discrimination_Tree
    val init_args = {
      empty_action = SOME (Library.K (PResults.empty_action Util.exn)),
      default_update = SOME Run.init_gpos,
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      prio_sq_co = SOME (PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.MEDIUM),
      progress = SOME Base_Data.AAMeta.P.Promising,
      del_select = SOME (apsnd (snd #> #thm #> the) #> Thm.eq_thm)}
    structure Log = Logging\<close>\<close>
end
end
\<close>
local_setup\<open>Zippy_Auto.Subst.setup_attribute NONE\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy Zippy_Auto.Subst.Concl; open ZLP MU; open SC A
    val id = @{binding subst_concl_some}
    val descr = Lazy.value "substitution in conclusion on some goal"
    fun tac ctxt thms = SELECT_GOAL
      (let fun apply_occ_tac occ st = Seq.of_list thms |> Seq.maps (fn r =>
        EqSubst.eqsubst_tac' ctxt
          (EqSubst.skip_first_occs_search occ EqSubst.searchf_lr_unify_valid) r
          (Thm.nprems_of st) st)
      in Seq.EVERY (List.map apply_occ_tac [0]) end)
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS_NONE_SOME_GOAL
      |> arr)
    val retrieval = Data.TI.content #> Library.K
    fun lookup ctxt = retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Subst.Asm; open ZLP MU; open SC A
    val id = @{binding subst_asm_some}
    val descr = Lazy.value "substitution in assumptions on some goal"
    fun tac ctxt thms = SELECT_GOAL
      (let fun apply_occ_tac occ st = Seq.of_list thms |> Seq.maps (fn r =>
        EqSubst.eqsubst_asm_tac' ctxt
          (EqSubst.skip_first_asm_occs_search EqSubst.searchf_lr_unify_valid) occ r
          (Thm.nprems_of st) st)
      in Seq.EVERY (List.map apply_occ_tac [0]) end)
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS_NONE_SOME_GOAL
      |> arr)
    val retrieval = Data.TI.content #> Library.K
    fun lookup ctxt = retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse \<open>(@{binding subst}, Zippy_Auto.Subst.parse_method)\<close>]]

paragraph \<open>Cases\<close>

ML\<open>
structure Zippy_Auto =
struct open Zippy_Auto
local open Zippy
in
\<^functor_instance>\<open>struct_name: Cases
  functor_name: Cases_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Cases = Cases_Tactic_HOL
    val init_config_data = {
      simp = SOME true,
      match = SOME (can Seq.hd oooo Type_Unification.e_unify Unification_Util.unify_types
        (Mixed_Unification.first_higherp_e_match Unification_Combinator.fail_match))}
    val parent_logger = Logger.root\<close>\<close>
end
end
\<close>
local_setup \<open>Zippy_Auto.Cases.setup_attribute NONE\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy Zippy_Auto.Cases; open ZLP MU; open SC A
    val id = @{binding cases}
    val prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.LOW
    val update_result = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    val tac = cases_tac (fn simp => fn opt_rule => fn insts => fn facts => fn ctxt =>
      Induct.cases_tac ctxt simp [insts] opt_rule facts)
    fun ztac args = tac args
      #> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.unclear
      #> Tac_AAM.Tac.zSOME_GOAL_FOCUS_NONE_SOME_GOAL
    fun mk_data ctxt args = {
      empty_action = Library.K (PResults.empty_action Util.exn),
      meta = Mixin4.Meta.Meta.metadata (id, Lazy.lazy (fn _ => Pretty.breaks [
          Pretty.str "cases on some goal with data",
          Cases_Data_Args.pretty_data ctxt args
        ] |> Pretty.block |> Pretty.string_of)),
      result_action = Result_Action.changed_goals_action update_result mk_cud,
      prio_sq_co = prio_sq_co,
      tac = Ctxt.with_ctxt (ztac args #> arr)}
    fun init _ focus = Ctxt.with_ctxt (fn ctxt =>
      let val update_focus_list = Data.get (Context.Proof ctxt)
        |> map (Cases_Data_Args.transfer_data (Proof_Context.theory_of ctxt) #> mk_data ctxt
          #> pair focus)
      in
        Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) update_focus_list
        >>> Up3.morph
      end)
  in (id, init) end\<close>]]
declare [[zippy_parse \<open>(@{binding cases}, Zippy_Auto.Cases.parse_context_update)\<close>]]

end
