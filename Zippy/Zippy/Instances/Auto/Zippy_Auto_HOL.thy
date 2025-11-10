\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Auto_HOL
  imports
    Cases_Tactics_HOL
    Extended_Blast_Data
    ML_Unification.ML_Unification_HOL_Setup
    Zippy_Instance_Cases
    Zippy_Instance_Classical
    Zippy_Instance_Induction
    Zippy_Instance_Subst
    Zippy_Auto_Pure
begin

paragraph \<open>Summary\<close>
text \<open>Setup the standard Zippy Auto instance.\<close>

paragraph \<open>Simplifier\<close>

declare [[zippy_parse del: \<open>@{binding simp}\<close>
  and add: \<open>(@{binding simp}, Zippy_Auto.Simp.parse_extended Splitter.split_modifiers)\<close>]]

paragraph \<open>Classical Reasoner\<close>

ML\<open>
local
  structure Base = struct structure Z = Zippy; structure Ctxt = Z.Ctxt end
  structure Zippy_Classical = Zippy_Instance_Classical(open Base)
in
structure Zippy = struct open Zippy_Classical Zippy end
structure Zippy_Auto =
struct open Zippy_Auto
\<^functor_instance>\<open>struct_name: Extended_Blast_Data
  functor_name: Extended_Blast_Data
  id: \<open>FI.prefix_id "blast"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val init_args = {depth = SOME 4, timeout = SOME 10.0}
    val parent_logger = Logging.logger
    \<close>\<close>
end
end
\<close>

declare [[zippy_init_gc \<open>
  let
    open Zippy; open ZLPC MU; open A Mo
    val id = @{binding classical_slow_step}
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    open Base_Data
    val costs_progress = ((Cost.VERY_LOW, AAMeta.P.promising), (Cost.LOW3, AAMeta.P.promising),
      (Cost.MEDIUM, AAMeta.P.unclear), (Cost.MEDIUM, AAMeta.P.unclear))
    val madd_safe = fst
    fun mk_meta (cost, progress) = A.K (Library.K (Library.K (AAMeta.metadata
      {cost = cost, progress = progress})))
    val (mk_meta_safe, mk_meta_inst0, mk_meta_instp, mk_meta_unsafe) =
      @{apply 4} mk_meta costs_progress
    val (presultsq_safe, presultsq_inst0, presultsq_instp, presultsq_unsafe) =
      @{apply 4} (fst #> Zippy_Auto.PResults.enum_scale_presultsq_default) costs_progress
    val data = Classical.slow_step_data Util.exn id update mk_cud madd_safe mk_meta_safe
      mk_meta_inst0 mk_meta_instp mk_meta_unsafe presultsq_safe presultsq_inst0 presultsq_instp
      presultsq_unsafe
    fun init _ focus z =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.no_descr id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gc \<open>
  let
    open Zippy; open ZLPC MU; open A Mo
    val id = @{binding atomize_prems}
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    open Base_Data
    val (cost, progress) = (Cost.LOW1, AAMeta.P.promising)
    val madd = fst
    val mk_meta = A.K (Library.K (Library.K (AAMeta.metadata {cost = cost, progress = progress})))
    val presultsq_atomize_prems = Zippy_Auto.PResults.enum_scale_presultsq_default cost
    val data = Classical.atomize_prems_data id update mk_cud madd mk_meta
      presultsq_atomize_prems
    fun init _ focus z =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.no_descr id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_parse add: \<open>(@{binding clasimp}, Clasimp.clasimp_modifiers |> Method.sections)\<close>
  \<open>(@{binding cla}, Classical.cla_modifiers |> Method.sections)\<close>
  and default: \<open>@{binding clasimp}\<close>]]

local_setup\<open>Zippy_Auto.Extended_Blast_Data.setup_attribute NONE\<close>
declare [[zippy_init_gc \<open>
  let
    open Zippy Zippy_Auto; open ZLPC MU; open A Mo Base_Data
    val id = @{binding blast}
    val (cost, progress, prio) = (Cost.VERY_LOW, AAMeta.P.promising, Cost.HIGH)
    val madd = fst
    val mk_meta = Library.K (Library.K (AAMeta.metadata {cost = cost, progress = progress}))
    val tac = Extended_Blast_Data.blast_tac
    fun ztac _ = Ctxt.with_ctxt (fn ctxt => arr (Tac_AAM.Tac.zTRY_EVERY_FOCUS1 madd
      (Tac_AAM.lift_tac mk_meta (tac ctxt))))
    val presultsq = Zippy_Auto.PResults.enum_scale_presultsq_default prio
    val data = {
      empty_action = Library.K Zippy.PAction.disable_action,
      meta = AMeta.metadata (id, Lazy.value "blast with depth and timeout limit"),
      result_action = Result_Action.action (Library.K (C.id ())) Result_Action.copy_update_data,
      presultsq = presultsq,
      tac = ztac}
    fun init _ focus z = Tac.cons_action_cluster Util.exn (ACMeta.no_descr id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_parse \<open>(@{binding blast}, Scan.depend (fn context =>
  Zippy_Auto.Extended_Blast_Data.parse_attribute
  >> (fn attr => (ML_Attribute_Util.attribute_map_context attr context, ()))))\<close>]]

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
    val cost = Cost.MEDIUM
    open Base_Data.AAMeta
    val init_args = {
      empty_action = SOME (Library.K PAction.disable_action),
      default_update = SOME Zippy_Auto.Run.init_gpos,
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      presultsq = SOME (Zippy_Auto.PResults.enum_scale_presultsq_default cost),
      mk_meta = SOME (Library.K (Library.K (metadata {cost = cost, progress = P.promising}))),
      del_select = SOME (apsnd (snd #> #thm #> the) #> Thm.eq_thm)}
    structure Log = Logging\<close>\<close>
end
end
\<close>
local_setup\<open>Zippy_Auto.Subst.setup_attribute NONE\<close>

declare [[zippy_init_gc \<open>
  let
    open Zippy Zippy_Auto.Subst.Concl; open ZLPC MU; open SC A Mo
    val id = @{binding subst_concl_some}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "substitution in conclusion on some goal")
    fun tac ctxt thms = SELECT_GOAL
      (let fun apply_occ_tac occ st = Seq.of_list thms |> Seq.maps (fn r =>
        EqSubst.eqsubst_tac' ctxt
          (EqSubst.skip_first_occs_search occ EqSubst.searchf_lr_unify_valid) r
          (Thm.nprems_of st) st)
      in Seq.EVERY (List.map apply_occ_tac [0]) end)
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
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
    open Zippy Zippy_Auto.Subst.Asm; open ZLPC MU; open SC A Mo
    val id = @{binding subst_asm_some}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "substitution in assumptions on some goal")
    fun tac ctxt thms = SELECT_GOAL
      (let fun apply_occ_tac occ st = Seq.of_list thms |> Seq.maps (fn r =>
        EqSubst.eqsubst_asm_tac' ctxt
          (EqSubst.skip_first_asm_occs_search EqSubst.searchf_lr_unify_valid) occ r
          (Thm.nprems_of st) st)
      in Seq.EVERY (List.map apply_occ_tac [0]) end)
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
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
    open Base_Data
    structure Z = Zippy
    structure Ctxt = Ctxt
    fun mk_init_args cost = {
      simp = SOME true,
      match = SOME (can Seq.hd oooo Type_Unification.e_unify Unification_Util.unify_types
        (Mixed_Unification.first_higherp_e_match Unification_Combinator.fail_match)),
      empty_action = SOME (Library.K Zippy.PAction.disable_action),
      default_update = SOME Zippy_Auto.Run.init_gpos,
      mk_cud = SOME Zippy.Result_Action.copy_update_data_empty_changed,
      presultsq = SOME (Zippy_Auto.PResults.enum_scale_presultsq_default cost),
      mk_meta = SOME (Library.K (Library.K (AAMeta.metadata
        {cost = cost, progress = AAMeta.P.promising})))}
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
    val init_args = mk_init_args Cost.MEDIUM
  \<close>\<close>
structure Cases = Cases.Cases_Data
\<^functor_instance>\<open>struct_name: Induction
  functor_name: Zippy_Instance_Induction_Data
  FI_struct_name: FI_Induction_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base_Args
    val init_args = mk_init_args Cost.HIGH
  \<close>\<close>
structure Induction = Induction.Induction_Data
end
end
\<close>
local_setup \<open>Zippy_Auto.Cases.setup_attribute NONE\<close>
local_setup \<open>Zippy_Auto.Induction.setup_attribute NONE\<close>

declare [[zippy_init_gc \<open>
  let open Zippy Zippy_Auto.Cases; open ZLPC MU; open SC A Mo
    val id = @{binding cases_some}
    val meta = Base_Data.ACMeta.metadata (id, Lazy.value "cases on some goal")
    val tac = Cases_Data_Args_Tactic_HOL.cases_tac (fn simp => fn opt_rule => fn insts =>
      fn facts => fn ctxt => Induct.cases_tac ctxt simp [insts] opt_rule facts)
    fun ztac mk_meta data _ = Ctxt.with_ctxt (fn ctxt => tac data ctxt
      |> Tac_AAM.lift_tac mk_meta
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
declare [[zippy_init_gc \<open>let open Zippy Zippy_Auto.Induction; open ZLPC MU; open SC A Mo
    val id = @{binding induct_some}
    val meta = Base_Data.ACMeta.metadata (id, Lazy.value "induction on some goal")
    val tac = Induction_Data_Args_Tactic_HOL.induct_tac false
    fun ztac mk_meta data _ = Ctxt.with_ctxt (fn ctxt => tac data ctxt
      |> Tac_AAM.lift_tac mk_meta
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
