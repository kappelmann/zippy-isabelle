\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Examples
  imports
    Zippy.ML_Priority_Queues
    Zippy.Zippy_Instance
    Main
begin

text \<open>Some simple examples showcasing navigation in the zipper and the creation of theorems using
the best-first search presented in the Zippy paper.\<close>

text \<open>Figure 6 from the paper.

Exhaustively run all rules and apply as tactic. Of course, this is only to show how the zipper
works and not meant for production. When used in practice, one should return results as soon as
there are no more subgoals in one of the tree's branches.\<close>

ML\<open>
local
  open Zippy
  open MU MEU
  open SC Mo A
in
end
\<close>

lemma silly: "A \<Longrightarrow> B" sorry
lemma cheat : "A" sorry

declare[[ML_print_depth=100]]
schematic_goal shows "?A \<and> B" "C \<and> D"
ML_prf\<open>open Zippy Zippy.MU.Mo\<close>
apply (tactic \<open>fn state =>
  let
    fun run _ =
      (*initialise the zipper*)
      (Util.init_thm_state state
      (*add actions*)
      >>= Down1.move
      >>= Tac_Util.cons_single_ztactic_action_cluster
        (NCo3.Meta.Meta.empty @{binding cluster1})
        (Util.result_tail_presults_action I)
        (NCo4.Meta.Meta.empty @{binding action1})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (ZS.with_state I
          (Tac_Util.resolve_moved_tac Zippy_Action_App_Progress.promising @{thms cheat silly} #> arr))
        (Tac.GPU.F.Goals [1])
      >>= Up3.move
      >>= Tac_Util.cons_single_ztactic_action_cluster
        (NCo3.Meta.Meta.empty @{binding cluster2})
        (Util.result_tail_presults_action I)
        (NCo4.Meta.Meta.empty @{binding action2})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (ZS.with_state I (Tac_Util.cheat_tac #> arr))
        (Tac.GPU.F.Goals [1])
      >>= Up3.move
      >>= Z2.ZM.Down.move
      >>= Tac_Util.cons_single_ztactic_action_cluster
        (NCo3.Meta.Meta.empty @{binding cluster3})
        (Util.result_tail_presults_action I)
        (NCo4.Meta.Meta.empty @{binding action3})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (ZS.with_state I (Tac_Util.cheat_tac #> arr))
        (Tac.GPU.F.Goals [1])
      >>= ZB.top3
      >>= Z1.ZM.Unzip.move
      (*get the theorems*)
      (* >>= Z1.ZM.Zip.move *)
      (* >>= Util.with_state Util.finish_promising_gclusters_oldest_first *)
      (*run best-first-search*)
      >>= SRuns.init_repeat_step_queue I
        (ZS.with_state I SRuns.mk_df_post_unreturned_unfinished_statesq) (SOME 0)
      )
      |> SRuns.seq_from_monad @{context}
      |> Seq.pull |> (fn sq => Seq.make (fn _ => sq))
    val (time, ressq) = Timing.timing run () |> apfst @{print}
  in
    let val _ =
      (* Seq.list_of statesq  *)
      (* |> List.map (snd #> fst #> fst #> Zippy.ZN.ZCore.N1.Co.getter
        #> Zippy.NCo1.CB.get_results
        #> Zippy.NCo1.Results.R.get_states
        #> Seq.list_of)  *)
      (* |> @{print} *)
      ()
    in
      ressq
      (* |> Seq.filter SRuns.is_finished  *)
      |> Seq.map (SRuns.get_result_data #> #thm_states) |> Seq.flat
    end
  end
\<close>)
(*you can backtrack with "back"*)
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
oops

text \<open>Search tree akin to Figure 1 from the paper.\<close>

lemma shows "A \<Longrightarrow> (B \<longrightarrow> C) \<or> (A \<and> A)"
apply (tactic \<open>fn state =>
  let
    val amd = amd ()
    val opt_statesq =
      (*initialise the zipper*)
      (init_thm_state' mk_gcd_more state >>= arr snd
      (*add the resolution tactics to the goal cluster*)
      >>= Down1.move
      (*one could, of course, also split each theorem into a separate action*)
      >>= with_state (zippy_resolve_tac RMD.promising @{thms conjI impI disjI1 disjI2}
          #> add_tac amd P.HIGH (F.goals [1]))
      >>= Up4.move >>= Up3.move
      (*add the assumption tactic to the goal cluster*)
      >>= with_state (assume_tac #> zippy_tac RMD.promising #> add_tac amd P.HIGH (F.goals [1]))
      >>= top4 >>= Z1.ZM.Unzip.move
      (*repeat best-first-search until no more changes*)
      >>= repeat_fold_pactions_max_df NONE
      (*get the theorems*)
      >>= Z1.ZM.Zip.move >>= with_state finish_gclusters_oldest_first)
      (*pass context to state monad*)
      |> MS.eval @{context}
  in
    case opt_statesq of
      NONE => Seq.empty
    | SOME statesq =>
        let val _ = Seq.list_of statesq |> @{make_string} |> writeln
        in statesq end
  end
\<close>)
(*you can backtrack with "back"*)
back
back (*solved branch*)
back
back
back
back (*etc.*)
oops

text \<open>Example with meta variable clusters, navigation, and printing.\<close>

schematic_goal shows "A \<and> ?B" "?B \<and> C" "D"
ML_val\<open>
val amd = amd ()
val state = @{Isar.goal} |> #goal
val opt_statesq =
  (*initialise the zipper*)
  (init_thm_state' mk_gcd_more state >>= arr snd
  (*print the goal clusters*)
  >>= (fn z => with_state pretty_gcs z >>= arr Pretty.writeln >>= arr (K z))
  >>= Down1.move
  (*print the first goal cluster*)
  >>= (fn z => with_state pretty_gc z >>= arr Pretty.writeln >>= arr (K z))
  (*add cheat tac focused on first subgoal of first goal cluster*)
  >>= with_state (cheat_tac RMD.promising #> add_tac amd P.VERY_HIGH (F.goals [1]))
  (*print the first action*)
  >>= (fn z => pretty_action z >>= arr Pretty.writeln >>= arr (K z))
  >>= Up4.move >>= Up3.move
  (*add cheat tac focused on second subgoal of first goal cluster*)
  >>= with_state (cheat_tac RMD.promising #> add_tac amd P.MEDIUM (F.goals [2]))
  (*print the second action*)
  >>= (fn z => pretty_action z >>= arr Pretty.writeln >>= arr (K z))
  >>= Up4.move >>= Up3.move >>= Z2.ZM.Down.move
  (*print the second goal cluster*)
  >>= (fn z => with_state pretty_gc z >>= arr Pretty.writeln >>= arr (K z))
  (*print the local location*)
  >>= (fn z => L.get (pos2 ()) z >>= arr (@{make_string} #> writeln) >>= arr (K z))
  (*add cheat tac focused on any subgoal of second goal cluster*)
  >>= with_state (cheat_tac RMD.promising #> add_tac amd P.LOW F.none)
  (*print the third action*)
  >>= (fn z => pretty_action z >>= arr Pretty.writeln >>= arr (K z))
  >>= top4 >>= Z1.ZM.Unzip.move
  (*repeat best-first-search for 4 steps*)
  >>= repeat_fold_pactions_max_df (SOME 4)
  (*get the theorems*)
  >>= Z1.ZM.Zip.move >>= with_state finish_gclusters_oldest_first >>= arr Seq.list_of
  ) |> MS.eval @{context} (*pass context to state monad*)
\<close>
oops

end
