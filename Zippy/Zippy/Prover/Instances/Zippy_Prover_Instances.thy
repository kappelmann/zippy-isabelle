\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover_Instances
  imports
    ML_Typeclasses.ML_State
    ML_Unification.ML_Priorities
    Zippy_Prover_Action_Metadata
    Zippy_Prover_Action_Cluster_Metadata
    Zippy_Prover_Metadata_Data
    Zippy_Prover_Position
    Zippy_Prover_Result_Metadata
begin

(*TODO: ordering including prios and non-closed subgoals*)
paragraph \<open>Summary\<close>
text \<open>The standard Zippy prover instance, using a state monad.\<close>

ML_file\<open>zippy_prover_instance_base.ML\<close>
ML_file\<open>zippy_prover_instance.ML\<close>

ML_file\<open>zippy.ML\<close>

lemma test: "PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP G \<Longrightarrow> PROP B \<Longrightarrow> (PROP A \<Longrightarrow> PROP A) \<Longrightarrow> PROP E \<Longrightarrow> PROP A &&& PROP B &&& PROP C &&& PROP D &&& PROP E &&& PROP F &&& PROP G" sorry

consts A :: "prop"
consts B :: "prop"
consts G :: "prop"
consts E :: "prop"
consts C :: "prop"
consts D :: "prop"
consts F :: "prop"
lemmas test_inst = test[of "PROP A" "PROP B" "PROP G" "PROP E" "PROP C" "PROP D" "PROP F"]

(* lemma "A \<equiv> B \<Longrightarrow> A \<equiv> C" *)
  (* apply simp *)

lemma cheat: "PROP P" sorry

declare[[ML_print_depth=100]]
ML\<open>
  local structure SC = Semi_Category(Zippy); structure C = Category(Zippy); structure M = Monad(Zippy.M)
    open SC Zippy M
  in
    fun halve_prio_co p = update_prio_co (fn _ => P.halve) p
    (* val presults_from_tac = Z.presults_from_tac' @{context} *)
    fun cheat_tac ctxt = resolve_tac ctxt [@{thm cheat}]
      |> lift_all_goals_focus_tac (K (Zippy_Result_Metadata.metadata RMD.promising))
        T.single_goal_empty_target
    val acmd = ACMD.metadata (@{binding "test cluster"}, "cluster description")
    val amd = AMD.metadata (@{binding "test action"}, "action description")
    fun add_tac p f ctxt z =
      acmd
      >>= (fn acmd => amd
      >>= (fn amd => cons_move_tac acmd amd (halve_prio_co p) (cheat_tac ctxt) f z))
    (* (halve_prio_co p) (cheat_tac mk_rmd ctxt) *)
    val test = Timing.timeit
      (fn _ => (
      (init_state' mk_gcsd_more mk_gcd_more
      >>> arr snd
      >>> Down1.move
      >>> with_state (add_tac P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (add_tac P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (add_tac P.LOW F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (add_tac P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Up2.move >>> Z1.ZM.Unzip.move
      >>> repeat_fold_run_max_paction_dfs NONE
      >>> Z1.ZM.Zip.move
      (* >>> \<^imap>\<open>\<open>{i}\<close> => \<open>Down{i}.move\<close> where sep = ">>>" and stop = 2\<close> *)
      (* >>> Up5.move *)
      (* >>> Z3.ZM.Down.move *)
      (* >>> pretty_actionc *)
      (* >>> top4 *)
      (* >>> Z1.ZM.Zip.move *)
      >>> finish_gclusters_oldest_first @{context}
      (* >>> up *)
      (* >>> L.get (L.lens_snd (L.id ())) *)
      (* >>> finish_gclusters_oldest_first @{context} *)
      )
      |> (fn f => f (@{thm test} |> Goal.protect 6) |> MS.eval @{context})
      ))
      |> the |> Seq.list_of
  end
\<close>

end
