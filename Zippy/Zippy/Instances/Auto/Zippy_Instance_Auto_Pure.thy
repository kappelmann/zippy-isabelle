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
structure Zippy = struct open Zippy_Simp Zippy end
end\<close>

ML\<open>
local val default_presultsq_scale = Rat.make (12, 10)
in
\<^functor_instance>\<open>struct_name: Zippy_Auto
  functor_name: Zippy_Instance_Auto
  id: \<open>"zippy"\<close>
  more_args: \<open>
    structure Z = Zippy
    open Z; open MU.A
    structure TI = Discrimination_Tree
    val cost = Cost.MEDIUM
    open Base_Data.AAMeta
    val resolve_init_args = {
      empty_action = SOME (Library.K PAction.disable_action),
      default_update = NONE,
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      presultsq = SOME (PResults.enum_scale_presultsq default_presultsq_scale cost),
      mk_meta = SOME (Library.K (Library.K (metadata {cost = cost, progress = P.promising}))),
      del_select = SOME (apsnd (snd #> #thm #> the) #> Thm.eq_thm)}
    val simp_init_args = {timeout = SOME 7.0, depth = NONE}
    structure Log_Base = Z.Logging.Base\<close>\<close>
structure Zippy_Auto =
struct open Zippy_Auto
structure PResults =
struct
val default_presultsq_scale = default_presultsq_scale
val enum_scale_presultsq_default = Zippy.PResults.enum_scale_presultsq default_presultsq_scale
end
end
end
\<close>
local_setup\<open>Zippy_Auto.Run.Init_Goal_Cluster.Data.setup_attribute
  (Either.Right "goal cluster initialisation")\<close>
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
struct open Run
local open Zippy; open ZLPC MU; open SC A Mo
  structure GC = Zippy_Goal_Cluster_Mixin(Mixin_Base2.GCluster)
in
fun init st = st |>
  (Util.init_thm_state >>> Down1.morph >>> Z2.ZM.Unzip.morph
  >>> Init_Goal_Cluster.update_all (Library.K Util.exn)
    (arr (GC.get_ngoals #> Base_Data.Tac_Res.GPU.F.all_upto))
  >>> top2 >>> Z1.ZM.Unzip.morph)

fun run_best_first x = Zippy.Run.run_statesq' Zippy.Run.Best_First.PAction_Queue.init_pactions_queue
  Zippy.Run.Best_First.Step.step_queue x
fun run_depth_first x = Zippy.Run.run_statesq' Zippy.Run.Depth_First.PAction_Queue.init_pactions_queue
  Zippy.Run.Depth_First.Step.step_queue x
fun run_breadth_first x = Zippy.Run.run_statesq' Zippy.Run.Breadth_First.PAction_Queue.init_pactions_queue
  Zippy.Run.Breadth_First.Step.step_queue x

val are_thm_variants = apply2 Thm.prop_of #> Term_Util.are_term_variants
fun changed_uniquesq st = Seq.filter (fn st' => not (are_thm_variants (st, st')))
  #> Tactic_Util.unique_thmsq are_thm_variants

\<^functor_instance>\<open>struct_name: Tac
  functor_name: Zippy_Run_Data
  id: \<open>FI.prefix_id "run"\<close>
  path: \<open>FI.struct_op "Run"\<close>
  more_args: \<open>
    structure Z = ZLPC
    structure Ctxt = Ctxt
    structure Seq_From_Monad = Seq_From_Monad
    type run_config = int option
    val init_args = {
      init = SOME init,
      run = SOME (run_best_first Zippy.Run.mk_df_post_unreturned_promising_statesq),
      post = SOME (fn st => Ctxt.with_ctxt (fn ctxt =>
        arr (changed_uniquesq st #> Seq.maps (prune_params_tac ctxt))))}
    \<close>\<close>
fun tac fuel ctxt = Tac.tac fuel {ctxt = ctxt}
end
end
end
\<close>
local_setup\<open>Zippy_Auto.Context_Parsers.setup_attribute NONE\<close>
local_setup\<open>Zippy_Auto.Run.Tac.setup_attribute NONE\<close>
declare [[zippy_parse add: \<open>(@{binding run}, Zippy_Auto.Run.Tac.parse_context_update)\<close>]]

paragraph \<open>Method\<close>

local_setup \<open>
  let open Zippy Zippy_Auto.Run
    val parse_fuel = Parse_Util.option Parse.nat
    val parse = Scan.lift parse_fuel --| Zippy_Auto.Context_Parsers.parse
      >> (Method.SIMPLE_METHOD oo tac)
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

ML\<open>
structure Zippy =
struct open Zippy
structure Mixin2 =
struct
  structure GCluster = Zippy_Goal_Cluster_Mixin(Zippy.Mixin_Base2.GCluster)
end
end
\<close>

declare [[zippy_init_gc \<open>
  let
    open Zippy Zippy_Auto.Resolves.Resolve_Unif; open ZLPC MU; open SC A Mo
    val id = @{binding resolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "resolution with higher-order unification on first possible goal")
    val tac = resolve_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> snd #> Data.TI.norm_term
      #> retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals =
        lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.Resolve_Match; open ZLPC MU; open SC A Mo
    val id = @{binding resolve_ho_match_first}
    val descr = Lazy.value "resolution with higher-order matching on first possible goal"
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "resolution with higher-order matching on first possible goal")
    val tac = match_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> snd #> Data.TI.norm_term
      #> retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
(*TODO: could be made more efficient: we already know the indices of possibly matching premises when
seraching the term index but do not use that information in the subsequent (d/e)resolution*)
declare [[zippy_init_gc
  \<open>let
    open Zippy Zippy_Auto.Resolves.EResolve_Unif; open ZLPC MU; open SC A Mo
    val id = @{binding eresolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "e-resolution with higher-order unification on first possible goal")
    val tac = eresolve_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.EResolve_Match; open ZLPC MU; open SC A Mo
    val id = @{binding eresolve_ho_match_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "e-resolution with higher-order matching on first possible goal")
    val tac = ematch_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gc
  \<open>let
    open Zippy Zippy_Auto.Resolves.DResolve_Unif; open ZLPC MU; open SC A Mo
    val id = @{binding dresolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "d-resolution with higher-order unification on first possible goal")
    fun tac ctxt thms =
      let
        (*Tactic.make_elim allows no context passing but Thm.biresolution fails to certificate certain
        theorems without a context*)
        fun make_elim ctxt thm =
          let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
          in zero_var_indexes (resolve revcut_rl) end
      in eresolve_tac ctxt (List.map (make_elim ctxt) thms) end
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.DResolve_Match; open ZLPC MU; open SC A Mo
    val id = @{binding dresolve_ho_match_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "d-resolution with higher-order matching on first possible goal")
    fun tac ctxt thms =
      let
        fun make_elim ctxt thm =
          let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
          in zero_var_indexes (resolve revcut_rl) end
      in ematch_tac ctxt (List.map (make_elim ctxt) thms) end
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gc
  \<open>let
    open Zippy Zippy_Auto.Resolves.FResolve_Unif; open ZLPC MU; open SC A Mo
    val id = @{binding fresolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "f-resolution with higher-order unification on first possible goal")
    val tac = Unify_Resolve_Base.unify_fresolve_tac
      Higher_Order_Unification.norms Higher_Order_Unification.unify
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac thm ctxt
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zippy_Auto.Resolves.FResolve_Match; open ZLPC MU; open SC A Mo
    val id = @{binding fresolve_ho_match_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "f-resolution with higher-order matching on first possible goal")
    (*FIXME: use same matcher as in other match tactics*)
    val tac = Unify_Resolve_Base.unify_fresolve_tac
      Mixed_Unification.norms_first_higherp_match
      (Mixed_Unification.first_higherp_e_match Unification_Combinator.fail_match)
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac thm ctxt
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
     fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse \<open>(@{binding resolve}, Zippy_Auto.Resolves.parse_resolve_method)\<close>]]
declare [[zippy_parse \<open>(@{binding eresolve}, Zippy_Auto.Resolves.parse_eresolve_method)\<close>]]
declare [[zippy_parse \<open>(@{binding dresolve}, Zippy_Auto.Resolves.parse_dresolve_method)\<close>]]
declare [[zippy_parse \<open>(@{binding fresolve}, Zippy_Auto.Resolves.parse_fresolve_method)\<close>]]

paragraph \<open>Simplifier\<close>

declare [[zippy_init_gc \<open>
  let
    open Zippy; open ZLPC MU; open SC A Mo
    val name = "asm_full_simp"
    val id = Zippy_Identifier.make (SOME @{here}) name
    val tacs = (safe_asm_full_simp_tac, asm_full_simp_tac)
    fun f_timeout ctxt i state n time = (@{log Logger.WARN Zippy_Auto.Simp.logger} ctxt
      (fn _ => Pretty.breaks [
          Pretty.block [Pretty.str (name ^ " timeout at pull number "), SpecCheck_Show.int n,
            Pretty.str " after ", Pretty.str (Time.print time), Pretty.str " seconds."],
          Pretty.block [Pretty.str "Called on subgoal ", SpecCheck_Show.term ctxt (Thm.prem_of state i)],
          Pretty.str (implode ["Consider removing ", name,
            " for this proof, increase/disable the timeout, or check for looping simp rules."])
        ] |> Pretty.block0 |> Pretty.string_of);
      NONE)
    (*FIXME: why is the simplifier raising Option.Option in some cases?*)
    fun handle_option_exn_sq ctxt sq = Seq.make (fn _ =>
      sq |> Seq.pull |> Option.map (apsnd (handle_option_exn_sq ctxt))
      handle Option.Option => (@{log Logger.WARN Zippy_Auto.Simp.logger} ctxt (fn _ =>
          "Simplifier raised unexpected Option.Option exception. Returning NONE instead.");
        NONE))
    fun wrap_tac tac ctxt i state = Zippy_Auto.Simp.Extended_Data.wrap_simp_tac
      (f_timeout ctxt i state) (fn ctxt => handle_option_exn_sq ctxt oo tac ctxt) ctxt i state
    val (safe_tac, tac) = apply2 wrap_tac (safe_asm_full_simp_tac, asm_full_simp_tac)
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zippy_Auto.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    open Base_Data
    val costs_progress = ((Cost.LOW, AAMeta.P.promising), (Cost.LOW1, AAMeta.P.promising))
    val madd_safe = fst
    val madd_unsafe_every = AAMeta.add Cost.add
    fun mk_meta (cost, progress) = A.K (Library.K (Library.K (AAMeta.metadata
      {cost = cost, progress = progress})))
    val (mk_meta_safe, mk_meta_unsafe) = apply2 mk_meta costs_progress
    val (presultsq_safe, presultsq_unsafe) =
      apply2 (fst #> Zippy_Auto.PResults.enum_scale_presultsq_default) costs_progress
    val data = Simp.gen_data Util.exn id name safe_tac tac update mk_cud
      madd_safe madd_unsafe_every mk_meta_safe mk_meta_unsafe mk_meta_unsafe presultsq_safe
      presultsq_unsafe presultsq_unsafe
    fun init _ focus z = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse add: \<open>(@{binding simp}, Zippy_Auto.Simp.parse_extended [])\<close>
  and default: \<open>@{binding simp}\<close>]]

(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Run.Best_First.Logging.Step.logger Logger.ALL\<close>]] *)
(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Run.Best_First.Logging.Run.logger Logger.ALL\<close>]] *)
(* declare [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.ALL\<close>]] *)

(*
TODO: DFS and BFS
*)

end
