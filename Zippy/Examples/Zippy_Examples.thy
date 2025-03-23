\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Examples
  imports
    Zippy.Zippy_Prover_Instances
begin

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
  local
    structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Zippy)
    structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(Zippy)
    structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(Zippy.M)
    open SC Zippy M
  in
    structure Zippy_DFS = \<^eval>\<open>mk_name ["DFS_Postorder_Enumerable", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
      structure Base = struct structure AE = AE end
      structure Z =
        \<^imap>\<open>\<open>{i}\<close> => \<open>
        \<^eval>\<open>mk_name ["Rotate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(\<close> where stop = 3\<close>
        Zippy
        \<^imap>\<open>\<open>{i}\<close> => \<open>)\<close> where stop = 3\<close>
      \<^imap>\<open>\<open>{i}\<close> => \<open>
      structure E{i} = \<^eval>\<open>sfx_T_nargs "DFS_Postorder_Enumerable_Zipper_Moves"\<close>(
        open Base; structure Z = Z.Z{i}.ZM)\<close>\<close>
      structure AE = AE)
    fun halve_prio_co p = update_prio_co (fn _ => P.halve) p
    (* val presults_from_tac = Z.presults_from_tac' @{context} *)
    fun cheat_tac prog ctxt = resolve_tac ctxt [@{thm cheat}]
      |> lift_all_goals_focus_tac (K (Zippy_Result_Metadata.metadata prog))
        T.single_goal_empty_target
    val amd = AMD.metadata (@{binding "test action"}, "action description")
    fun add_tac amd p f tac z =
      amd >>= (fn amd => cons_move_tac amd (halve_prio_co p) tac f z)
    (* (halve_prio_co p) (cheat_tac mk_rmd ctxt) *)
    fun gen_fold_run_paction_dfs fold_paction =
      Zippy_DFS.first3 >>> fold_paction >>> fold_pactions_run_single_res
    fun gen_fold_max_paction_dfs update_res = fold_pactions_max P.ord update_res Zippy_DFS.next
    val test = Timing.timeit
      (fn _ => (
      (init_state' mk_gcd_more
      >>> arr snd
      >>> Down1.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.HIGH (F.goals [2]))
      (* >>> L.get (pos1 ()) *)
      >>> Up4.move >>> Up3.move
      >>> with_state (cheat_tac RMD.promising #> add_tac amd P.LOW (F.goals [2]))
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Z2.ZM.Down.move
      >>> with_state (cheat_tac RMD.unclear #> add_tac amd P.MEDIUM F.none)
      >>> Up4.move >>> Up3.move >>> Up2.move >>> Z1.ZM.Unzip.move
      >>> repeat_fold_run_max_paction_dfs_halve_prio_depth NONE
      (* >>> Zippy_DFS.first3 *)
      (* >>> L.get (depth4 ()) *)
      (* >>> repeat_fold_run_max_paction_dfs_halve_prio_depth (SOME 1) *)
      >>> Z1.ZM.Zip.move
      >>> Down1.move
      >>> Z2.ZM.Down.move
      >>> Down2.move
      >>> Down3.move
      >>> Down4.move
      (* >>> Down5.move *)
      (* >>> Down1.move  *)
      (* >>> Z2.ZM.Down.move *)
      >>> L.get (pos5 ())
      (* >>> Down1.move >>> Down2.move >>> Down3.move  *)
      (* >>> repeat_fold_run_max_paction_dfs_halve_prio_depth (SOME 1) *)
      (* >>> Z1.ZM.Unzip.move *)
      (* >>> Zippy_DFS.first3 *)
      (* >>> gen_fold_run_paction_dfs (gen_fold_max_paction_dfs (id ())) *)
      (* >>> (fn z => get_run_paction z >>= (fn x => run_action x z)) *)
      (* >>> Z1.ZM.Zip.move
      >>> (fn z => get_run_paction z >>= (fn x => run_action x z))
      >>> Down4.move >>> Down5.move >>> Down1.move  *)
      (* >>> run_action *)
      (* >>> Z.Zippy_DFS.first3 >>> fold_paction *)
      (* >>> fold_run_max_paction_dfs_halve_prio_depth *)
      (* >>> Z1.ZM.Zip.move *)
      (* >>> with_state pretty_gc *)
      (* >>> with_state pretty_gcs *)
      (* >>> pretty_actionc *)
      (* >>> pretty_action *)
      (* >>> finish_gclusters_oldest_first @{context} >>> arr (Seq.list_of) *)
      (* >>> finish_promising_gclusters_oldest_first @{context} >>> arr (Seq.list_of) *)
      )
      |> (fn f => f (Goal.protect 6 @{thm test}) |> MS.eval @{context})
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
