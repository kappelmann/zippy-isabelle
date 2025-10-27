\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Auto_HOL
  imports
    Cases_Tactics_HOL
    Extended_Blast_Data
    Zippy_Instance_Cases
    Zippy_Instance_Classical
    Zippy_Instance_Induction
    Zippy_Instance_Subst
    Zippy_Instance_Auto_Pure
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

declare [[zippy_init_gc \<open>
  let
    open Zippy; open ZLP MU; open A Mo
    val id = @{binding classical_slow_step}
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    val cresultsq_safe = CResults.enum_double_cost_double_cost_depth_cresultsq Cost.VERY_LOW
    val cresultsq_inst0 = CResults.enum_double_cost_double_cost_depth_cresultsq Cost.LOW3
    val cresultsq_instp = CResults.enum_double_cost_double_cost_depth_cresultsq Cost.MEDIUM
    val cresultsq_unsafe = CResults.enum_double_cost_double_cost_depth_cresultsq Cost.MEDIUM
    val data = Classical.slow_step_data Util.exn id update mk_cud
      cresultsq_safe cresultsq_inst0 cresultsq_instp cresultsq_unsafe
    fun init _ focus z =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gc \<open>
  let
    open Zippy; open ZLP MU; open A Mo
    val id = @{binding atomize_prems}
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    val cresultsq_atomize_prems = CResults.enum_double_cost_double_cost_depth_cresultsq Cost.LOW1
    val data = Classical.atomize_prems_data id update mk_cud
      cresultsq_atomize_prems
    fun init _ focus z =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_parse add: \<open>(@{binding clasimp}, Clasimp.clasimp_modifiers |> Method.sections)\<close>
  and default: \<open>@{binding clasimp}\<close>]]

local_setup\<open>Zippy_Auto.Extended_Blast_Data.setup_attribute NONE\<close>
declare [[zippy_init_gc \<open>
  let
    open Zippy Zippy_Auto; open ZLP MU; open A Mo
    val id = @{binding blast}
    val cresultsq = CResults.enum_double_cost_double_cost_depth_cresultsq Cost.HIGH
    val tac = Extended_Blast_Data.blast_tac
    val ztac = tac
      #> Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising
      #> Tac_AAM.Tac.zTRY_EVERY_FOCUS1 Tac_AAM.madd
    val data = {
      empty_action = Library.K CAction.disable_action,
      meta = Mixin_Base4.Meta.Meta.metadata (id, Lazy.value "blast with depth and timeout limit"),
      result_action = Result_Action.action (Library.K (C.id ())) Result_Action.copy_update_data,
      cresultsq = cresultsq,
      tac = Ctxt.with_ctxt (ztac #> arr)}
    fun init _ focus z = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
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
      PAA.cresultsq (Tac_Util.enum_double_cresultsq cost.VERY_HIGH)]
    val context = context
      |> fold (Zippy_Auto.Resolve_Match.insert_args_context_defaults args) sintro
      |> fold (Zippy_Auto.EResolve_Match.insert_args_context_defaults args) selim
      |> fold (Zippy_Auto.DResolve_Match.insert_args_context_defaults args) sdest

    val args = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates [],
      PAA.progress Base_Data.AAMeta.P.Promising,
      PAA.cresultsq (Tac_Util.enum_double_cost_double_cost_depth_cresultsq cost.HIGH)]
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

(* declare [[zippy_init_gc \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding auto_tac}
    fun tac ctxt = auto_tac ctxt |> CHANGED |> SELECT_GOAL
    fun ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1 Tac_AAM.madd
    val mk_cud = Result_Action.copy_update_data
    val action_data = {
      empty_action = CAction.disable_action,
      meta = Mixin_Base4.Meta.Meta.empty id,
      result_action = Result_Action.action (Library.K (C.id ())) mk_cud,
      cresultsq = CResults.enum_double_cost_double_cost_depth_cresultsq cost.HIGH,
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
      empty_action = SOME (Library.K CAction.disable_action),
      default_update = SOME Zippy_Auto.Run.init_gpos,
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      cresultsq = SOME (CResults.enum_double_cost_double_cost_depth_cresultsq Cost.MEDIUM),
      progress = SOME Base_Data.AAMeta.P.Promising,
      del_select = SOME (apsnd (snd #> #thm #> the) #> Thm.eq_thm)}
    structure Log = Logging\<close>\<close>
end
end
\<close>
local_setup\<open>Zippy_Auto.Subst.setup_attribute NONE\<close>

declare [[zippy_init_gc \<open>
  let
    open Zippy Zippy_Auto.Subst.Concl; open ZLP MU; open SC A Mo
    val id = @{binding subst_concl_some}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "substitution in conclusion on some goal")
    fun tac ctxt thms = SELECT_GOAL
      (let fun apply_occ_tac occ st = Seq.of_list thms |> Seq.maps (fn r =>
        EqSubst.eqsubst_tac' ctxt
          (EqSubst.skip_first_occs_search occ EqSubst.searchf_lr_unify_valid) r
          (Thm.nprems_of st) st)
      in Seq.EVERY (List.map apply_occ_tac [0]) end)
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.content #> Library.K
    fun lookup_goal ctxt = retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt =>
      Data.TI.content (Data.get_index (Context.Proof ctxt))
      |> List.map (snd #> transfer_data (Proof_Context.theory_of ctxt))
      |> map_index (fn (i, data) =>
        cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      |> ZB.update_zipper3)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Subst.Asm; open ZLP MU; open SC A Mo
    val id = @{binding subst_asm_some}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "substitution in assumptions on some goal")
    fun tac ctxt thms = SELECT_GOAL
      (let fun apply_occ_tac occ st = Seq.of_list thms |> Seq.maps (fn r =>
        EqSubst.eqsubst_asm_tac' ctxt
          (EqSubst.skip_first_asm_occs_search EqSubst.searchf_lr_unify_valid) occ r
          (Thm.nprems_of st) st)
      in Seq.EVERY (List.map apply_occ_tac [0]) end)
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
      |> arr)
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt =>
      Data.TI.content (Data.get_index (Context.Proof ctxt))
      |> List.map (snd #> transfer_data (Proof_Context.theory_of ctxt))
      |> map_index (fn (i, data) =>
        cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      |> ZB.update_zipper3)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse \<open>(@{binding subst}, Zippy_Auto.Subst.parse_method)\<close>]]

paragraph \<open>Cases and Induction\<close>

ML\<open>
structure Zippy_Auto =
struct open Zippy_Auto
local open Zippy
  structure Base_Args =
  struct
    structure Z = Zippy
    structure Ctxt = Ctxt
    fun mk_init_args cost = {
      simp = SOME true,
      match = SOME (can Seq.hd oooo Type_Unification.e_unify Unification_Util.unify_types
        (Mixed_Unification.first_higherp_e_match Unification_Combinator.fail_match)),
      empty_action = SOME (Library.K CAction.disable_action),
      default_update = SOME Zippy_Auto.Run.init_gpos,
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      cresultsq = SOME (CResults.enum_double_cost_double_cost_depth_cresultsq cost),
      progress = SOME Base_Data.AAMeta.P.Unclear}
    structure Log = Logging
    structure Log_Base = Logging.Base
    structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy
    structure Log_LGoals = Logging.LGoals
  end
in
\<^functor_instance>\<open>struct_name: Cases
  functor_name: Zippy_Instance_Cases_Data
  FI_struct_name: FI_Cases_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base_Args
    val init_args = mk_init_args Cost.HIGH
  \<close>\<close>
structure Cases = Cases.Cases_Data
\<^functor_instance>\<open>struct_name: Induction
  functor_name: Zippy_Instance_Induction_Data
  FI_struct_name: FI_Induction_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base_Args
    val init_args = mk_init_args Cost.VERY_HIGH
  \<close>\<close>
structure Induction = Induction.Induction_Data
end
end
\<close>
local_setup \<open>Zippy_Auto.Cases.setup_attribute NONE\<close>
local_setup \<open>Zippy_Auto.Induction.setup_attribute NONE\<close>

declare [[zippy_init_gc \<open>
  let open Zippy Zippy_Auto.Cases; open ZLP MU; open SC A Mo
    val id = @{binding cases_some}
    val meta = Base_Data.ACMeta.metadata (id, Lazy.value "cases on some goal")
    val tac = Cases_Data_Args_Tactic_HOL.cases_tac (fn simp => fn opt_rule => fn insts =>
      fn facts => fn ctxt => Induct.cases_tac ctxt simp [insts] opt_rule facts)
    fun ztac progress data = Ctxt.with_ctxt (fn ctxt => tac data ctxt
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
      |> arr)
    val opt_default_update_action = NONE
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => Data.get (Context.Proof ctxt)
      |> List.map (transfer_data (Proof_Context.theory_of ctxt))
      |> map_index (fn (i, data) =>
        cons_nth_action Util.exn meta ztac opt_default_update_action ctxt i data focus >>> Up4.morph)
      |> ZB.update_zipper3)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gc \<open>let open Zippy Zippy_Auto.Induction; open ZLP MU; open SC A Mo
    val id = @{binding induct_some}
    val meta = Base_Data.ACMeta.metadata (id, Lazy.value "induction on some goal")
    val tac = Induction_Data_Args_Tactic_HOL.induct_tac false
    fun ztac progress data = Ctxt.with_ctxt (fn ctxt => tac data ctxt
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zSOME_GOAL_FOCUS
      |> arr)
    val opt_default_update_action = NONE
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => Data.get (Context.Proof ctxt)
      |> List.map (transfer_data (Proof_Context.theory_of ctxt))
      |> map_index (fn (i, data) =>
        cons_nth_action Util.exn meta ztac opt_default_update_action ctxt i data focus >>> Up4.morph)
      |> ZB.update_zipper3)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_parse \<open>(@{binding cases}, Zippy_Auto.Cases.parse_context_update)\<close>]]
declare [[zippy_parse \<open>(@{binding induct}, Zippy_Auto.Induction.parse_context_update)\<close>]]

end
