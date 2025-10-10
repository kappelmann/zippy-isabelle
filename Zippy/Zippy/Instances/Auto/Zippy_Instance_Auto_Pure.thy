\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Auto_Pure
  imports
    Context_Parsers
    Zippy_Instance_Auto
    Zippy_Instance_Pure
    Zippy_Instance_Simp
begin

text \<open>Setup the standard instance with short name \<open>zippy\<close>.\<close>

ML\<open>
local
  structure Base = struct structure Z = Zippy; structure Ctxt = Z.Ctxt end
  structure Zippy_Simp = Zippy_Instance_Simp(open Base)
in
structure Zippy = struct open Zippy Zippy_Simp end
end\<close>

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
      del_select = SOME (apsnd (snd #> #thm #> the) #> Thm.eq_thm)}\<close>\<close>
\<close>
local_setup\<open>Zippy_Auto.Init_Goal_Clusters.Data.setup_attribute
  (Either.Right "goal clusters initialisation")\<close>
local_setup\<open>Zippy_Auto.Simp.Extended_Data.setup_attribute (Either.Right "extended simp")\<close>

ML\<open>
structure Zippy_Auto =
struct open Zippy_Auto
(* add parsers *)
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
fun init_gposs sort = (sort ? Library.sort int_ord)
  #> Base_Data.Tac_Res.GPU.F.goals #> Init_Goal_Clusters.init
val init_gpos = Base_Data.GFocus.single #> Init_Goal_Clusters.init

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

paragraph \<open>Method\<close>

local_setup \<open>
  let
    val parse_fuel = Parse_Util.option Parse.nat
    val parse = Scan.lift parse_fuel
      --| Zippy_Auto.Context_Parsers.parse
      >> (Method.SIMPLE_METHOD oo Zippy_Auto.Run.zippy_tac)
  in Method.local_setup @{binding zippy} parse "Extensible white-box prover based on Zippy" end\<close>

paragraph \<open>Resolution\<close>

local_setup\<open>Zippy_Auto.Resolves.setup_resolve_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.setup_eresolve_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.setup_dresolve_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Resolves.setup_fresolve_attribute NONE\<close>

declare [[zippy_resolve config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_resolve (match) config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_eresolve config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_eresolve (match) config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_dresolve config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_dresolve (match) config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_fresolve config default_update: Zippy_Auto.Run.init_gpos]]
and [[zippy_fresolve (match) config default_update: Zippy_Auto.Run.init_gpos]]

declare [[zippy_init_gcs \<open>
  let
    open Zippy Zippy_Auto.Resolves.Resolve_Unif; open ZLP MU; open SC A
    val id = @{binding resolve_ho_unif_first}
    val descr = Lazy.value "resolution with higher-order unification on first possible goal"
    val tac = resolve_tac
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> snd #> Data.TI.norm_term #>
      retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.Resolve_Match; open ZLP MU; open SC A
    val id = @{binding resolve_ho_match_first}
    val descr = Lazy.value "resolution with higher-order matching on first possible goal"
    val tac = match_tac
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> snd #> Data.TI.norm_term
      #> retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>]]
(*TODO: could be made more efficient: we already know the indices of possibly matching premises when
seraching the term index but do not use that information in the subsequent (d/e)resolution*)
declare [[zippy_init_gcs
  \<open>let
    open Zippy Zippy_Auto.Resolves.EResolve_Unif; open ZLP MU; open SC A
    val id = @{binding eresolve_ho_unif_first}
    val descr = Lazy.value "e-resolution with higher-order unification on first possible goal"
    val tac = eresolve_tac
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.EResolve_Match; open ZLP MU; open SC A
    val id = @{binding eresolve_ho_match_first}
    val descr = Lazy.value "e-resolution with higher-order matching on first possible goal"
    val tac = ematch_tac
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gcs
  \<open>let
    open Zippy Zippy_Auto.Resolves.DResolve_Unif; open ZLP MU; open SC A
    val id = @{binding dresolve_ho_unif_first}
    val descr = Lazy.value "d-resolution with higher-order unification on first possible goal"
    fun tac ctxt thms =
      let
        (*Tactic.make_elim allows no context passing but Thm.biresolution fails to certificate certain
        theorems without a context*)
        fun make_elim ctxt thm =
          let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
          in zero_var_indexes (resolve revcut_rl) end
      in eresolve_tac ctxt (List.map (make_elim ctxt) thms) end
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.DResolve_Match; open ZLP MU; open SC A
    val id = @{binding dresolve_ho_match_first}
    val descr = Lazy.value "d-resolution with higher-order matching on first possible goal"
    fun tac ctxt thms =
      let
        fun make_elim ctxt thm =
          let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
          in zero_var_indexes (resolve revcut_rl) end
      in ematch_tac ctxt (List.map (make_elim ctxt) thms) end
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gcs
  \<open>let
    open Zippy Zippy_Auto.Resolves.FResolve_Unif; open ZLP MU; open SC A
    val id = @{binding fresolve_ho_unif_first}
    val descr = Lazy.value "f-resolution with higher-order unification on first possible goal"
    val tac = Unify_Resolve_Base.unify_fresolve_tac
      Higher_Order_Unification.norms Higher_Order_Unification.unify
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac thm ctxt
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.FResolve_Match; open ZLP MU; open SC A
    val id = @{binding fresolve_ho_match_first}
    val descr = Lazy.value "f-resolution with higher-order matching on first possible goal"
    (*FIXME: use same matcher as in other match tactics*)
    val tac = Unify_Resolve_Base.unify_fresolve_tac
      Mixed_Unification.norms_first_higherp_match
      (Mixed_Unification.first_higherp_e_match Unification_Combinator.fail_match)
    fun ztac progress thm = Ctxt.with_ctxt (fn ctxt => tac thm ctxt
      |> Tac_AAM.lift_tac_progress progress
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS_NONE_FIRST_GOAL
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun init (_, goals) focus = Ctxt.with_ctxt (fn ctxt => cons_action_cluster Util.exn
        (Base_Data.ACMeta.metadata (id, descr)) ztac ctxt
        (focused_data_none_each (lookup ctxt) goals focus))
      >>> Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse \<open>(@{binding resolve}, Zippy_Auto.Resolves.parse_resolve_method)\<close>]]
declare [[zippy_parse \<open>(@{binding eresolve}, Zippy_Auto.Resolves.parse_eresolve_method)\<close>]]
declare [[zippy_parse \<open>(@{binding dresolve}, Zippy_Auto.Resolves.parse_dresolve_method)\<close>]]
declare [[zippy_parse \<open>(@{binding fresolve}, Zippy_Auto.Resolves.parse_fresolve_method)\<close>]]

paragraph \<open>Simplifier\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy; open ZLP MU; open SC
    val name = "asm_full_simp"
    val tacs = (safe_asm_full_simp_tac, asm_full_simp_tac)
    val id = Zippy_Identifier.make (SOME @{here}) name
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    val prio_sq_co_safe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH1
    val prio_sq_co_unsafe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH
    fun f_timeout ctxt i state n time = (@{log Logger.WARN Zippy_Auto.Simp.logger} ctxt
      (fn _ => Pretty.breaks [
          Pretty.block [Pretty.str (name ^ " timeout at pull number "), SpecCheck_Show.int n,
            Pretty.str " after ", Pretty.str (Time.print time), Pretty.str " seconds."],
          Pretty.block [Pretty.str "Called on subgoal ", SpecCheck_Show.int i, Pretty.str " of state ",
            Thm.pretty_thm ctxt state],
          Pretty.str (implode ["Consider removing ", name,
            " for this proof, increase/disable the timeout, or check for looping simp rules."])
        ] |> Pretty.block0 |> Pretty.string_of);
      NONE)
    fun wrap_tac tac ctxt i state = Zippy_Auto.Simp.Extended_Data.wrap_simp_tac
      (f_timeout ctxt i state) tac ctxt i state
    val (safe_tac, tac) = apply2 wrap_tac tacs
    val data = Simp.gen_data name safe_tac tac Util.exn id update mk_cud
      prio_sq_co_safe prio_sq_co_unsafe
    fun init _ focus = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)]
      >>> Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse add: \<open>(@{binding simp}, Zippy_Auto.Simp.parse_extended [])\<close>
  and default: \<open>@{binding simp}\<close>]]

(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Run_Best_First.Logging.Step.logger Logger.ALL\<close>]] *)
(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Run_Best_First.Logging.Run.logger Logger.ALL\<close>]] *)
(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.ALL\<close>]] *)

(*TODO:
- A^* (1/prio = cost VS (0, 1))
*)

end
