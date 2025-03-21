\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover_Instances
  imports
    ML_Typeclasses.ML_State
    ML_Unification.ML_Priorities
    Zippy_Prover_Action_Metadata
    Zippy_Prover_Action_Cluster_Metadata
    Zippy_Prover_Goal_Clusters_Metadata
    Zippy_Prover_Metadata_Data
    Zippy_Prover_Position
    Zippy_Prover_Result_Metadata
begin

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
    fun halve_prio_co p = update_prio_co (fn _ => P.halve) (P.double p)
    (* val presults_from_tac = Z.presults_from_tac' @{context} *)
    fun cheat_tac prog ctxt = resolve_tac ctxt [@{thm cheat}]
      |> lift_all_goals_focus_tac (K (Zippy_Result_Metadata.metadata prog))
        T.single_goal_empty_target
    val amd = AMD.metadata (@{binding "test action"}, "action description")
    fun add_tac amd p f tac z =
      amd >>= (fn amd => cons_move_tac amd (halve_prio_co p) tac f z)
    (* (halve_prio_co p) (cheat_tac mk_rmd ctxt) *)
    val test = Timing.timeit
      (fn _ => (
      (init_state' mk_gcd_more
      >>> arr snd
      >>> Down1.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.HIGH (F.none))
      (* >>> Up4.move >>> Up3.move *)
      (* >>> with_state (cheat_tac RMD.promising #> add_tac amd P.LOW (F.goals [2])) *)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Up2.move >>> Z1.ZM.Unzip.move
      >>> repeat_fold_run_max_paction_dfs_halve_prio_depth NONE
      >>> Z1.ZM.Zip.move
      (* >>> Down1.move
      >>> Down2.move >>> Down3.move
      >>> Down4.move
      >>> Down5.move
      >>> Down1.move
      >>> Down2.move >>> Down3.move *)
      (* >>> top1 *)
      (* >>> Down1.move >>> Down2.move >>> Down3.move >>> Down4.move >>> Down5.move *)
      (* >>> Down4.move *)
      (* >>> Down5.move  *)
      (* >>> with_state pretty_gcs *)
      (* >>> pretty_actiona *)
      (* >>> \<^imap>\<open>\<open>{i}\<close> => \<open>Down{i}.move\<close> where sep = ">>>" and stop = 2\<close> *)
      (* >>> Up5.move *)
      (* >>> Z3.ZM.Down.move *)
      (* >>> pretty_actionc *)
      (* >>> top4 *)
      (* >>> Z1.ZM.Zip.move *)
      (* >>> finish_gclusters_oldest_first @{context} >>> arr (Seq.list_of) *)
      >>> finish_promising_gclusters_oldest_first @{context} >>> arr (Seq.list_of)
      (* >>> up *)
      (* >>> L.get (L.lens_snd (L.id ())) *)
      (* >>> finish_gclusters_oldest_first @{context} *)
      )
      |> (fn f => f (@{thm test} |> Goal.protect 6) |> MS.eval @{context})
      ))
  end
\<close>

(*

GCS
|       |
GC      GC
|   |    |
AC  AC   AC
| |  |    |
A A  A    A
|    |    |
AA   AA   AA
|    |    |
GCS  GCS  GCS

*)

end
