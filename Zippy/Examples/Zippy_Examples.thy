\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Examples
  imports
    Zippy.ML_Priority_Queues
    Zippy.Zippy_Instance
    Main
    ML_Unification.ML_Term_Index
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
  open MU
  open SC Mo A
in
end
\<close>

lemma silly: "A \<Longrightarrow> B" sorry
lemma cheat : "A" sorry

declare[[ML_print_depth=100]]
schematic_goal shows "?A \<and> B" "?C \<and> D"
ML_prf\<open>open Zippy; open MU; open Mo A\<close>
supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.Run.logger Logger.DEBUG\<close>]]
supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.Step.logger Logger.DEBUG\<close>]]
apply (tactic \<open>fn state =>
  let
    val with_ctxt = Ctxt.with_ctxt
    fun run _ =
      (*initialise the zipper*)
      (Util.init_thm_state state
      (*add actions*)
      >>= Down1.morph
      >>= Tac_Util.cons_single_ztactic_action_cluster'
        (Mixin3.Meta.Meta.empty @{binding cluster1})
        (Mixin4.Meta.Meta.empty @{binding action1})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (with_ctxt
          (Tac_Util.resolve_moved_ztac Mixin5.Meta.Meta.P.promising @{thms cheat silly} #> arr))
        (Tac.GPU.F.Goals [1])
      >>= Up3.morph
      >>= Tac_Util.cons_single_ztactic_action_cluster'
        (Mixin3.Meta.Meta.empty @{binding cluster2})
        (Mixin4.Meta.Meta.empty @{binding action2})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (with_ctxt (Tac_Util.cheat_ztac #> arr))
        (Tac.GPU.F.Goals [1])
      >>= Up3.morph
      >>= Z2.ZM.Down.morph
      >>= Tac_Util.cons_single_ztactic_action_cluster'
        (Mixin3.Meta.Meta.empty @{binding cluster3})
        (Mixin4.Meta.Meta.empty @{binding action3})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (with_ctxt (Tac_Util.cheat_ztac #> arr))
        (Tac.GPU.F.Goals [1])
      >>= ZB.top3
      >>= Z1.ZM.Unzip.morph
      (*run best-first-search*)
      >>= Run.init_repeat_step_queue
        (with_ctxt Run.mk_df_post_unreturned_unfinished_statesq) NONE
      )
      |> Run.seq_from_monad {ctxt = @{context}, state = ()}
      |> Seq.map (Run.get_result_data #> #thm_states) |> Seq.flat |> Tactic_Util.unique_thmsq |> Seq.list_of |> Seq.of_list
      (* |> Seq.pull |> (fn sq => Seq.make (fn _ => sq)) *)
    val (time, ressq) = Timing.timing run () |> apfst @{print}
  in ressq end
\<close>)
(*you can backtrack with "back"*)
back
back
back
back
oops

text \<open>Search tree akin to Figure 1 from the paper.\<close>

schematic_goal shows "A \<Longrightarrow> (B \<longrightarrow> C) \<or> (A \<and> A)"
ML_prf\<open>open Zippy; open MU; open Mo A SC\<close>
supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.Run.logger Logger.TRACE\<close>]]
supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.Step.logger Logger.DEBUG\<close>]]
apply (tactic \<open>fn state =>
  let
    val with_ctxt = Ctxt.with_ctxt
    fun run _ =
      (*initialise the zipper*)
      (Util.init_thm_state state
      (*add actions*)
      >>= Down1.morph
      >>= Tac_Util.cons_single_ztactic_action_cluster'
        (Mixin3.Meta.Meta.empty @{binding cluster1})
        (Mixin4.Meta.Meta.empty @{binding action1})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (with_ctxt
          (Tac_Util.resolve_moved_ztac Mixin5.Meta.Meta.P.promising @{thms conjI impI disjI1 disjI2} #> arr))
        (Tac.GPU.F.Goals [1])
      >>= Up3.morph
      >>= Tac_Util.cons_single_ztactic_action_cluster'
        (Mixin3.Meta.Meta.empty @{binding cluster2})
        (Mixin4.Meta.Meta.empty @{binding action2})
        (Tac_Util.halve_prio_halve_prio_depth_res_co Prio.HIGH)
        (with_ctxt (Tac_Util.assume_moved_ztac #> arr))
        (Tac.GPU.F.Goals [1])
      >>= ZB.top3
      >>= Z1.ZM.Unzip.morph
      (*run best-first-search*)
      >>= Run.init_repeat_step_queue
        (with_ctxt Run.mk_df_post_unreturned_unfinished_statesq) NONE
      )
      |> Run.seq_from_monad {ctxt = @{context}, state = ()}
      |> Seq.map (Run.get_result_data #> #thm_states) |> Seq.flat |> Tactic_Util.unique_thmsq |> Seq.list_of |> Seq.of_list
    val (time, ressq) = Timing.timing run () |> apfst @{print}
  in
    ressq
  end
\<close>)
done

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
  >>= Down1.morph
  (*print the first goal cluster*)
  >>= (fn z => with_state pretty_gc z >>= arr Pretty.writeln >>= arr (K z))
  (*add cheat tac focused on first subgoal of first goal cluster*)
  >>= with_state (cheat_tac RMD.promising #> add_tac amd P.VERY_HIGH (F.goals [1]))
  (*print the first action*)
  >>= (fn z => pretty_action z >>= arr Pretty.writeln >>= arr (K z))
  >>= Up4.morph >>= Up3.morph
  (*add cheat tac focused on second subgoal of first goal cluster*)
  >>= with_state (cheat_tac RMD.promising #> add_tac amd P.MEDIUM (F.goals [2]))
  (*print the second action*)
  >>= (fn z => pretty_action z >>= arr Pretty.writeln >>= arr (K z))
  >>= Up4.morph >>= Up3.morph >>= Z2.ZM.Down.morph
  (*print the second goal cluster*)
  >>= (fn z => with_state pretty_gc z >>= arr Pretty.writeln >>= arr (K z))
  (*print the local location*)
  >>= (fn z => L.get (pos2 ()) z >>= arr (@{make_string} #> writeln) >>= arr (K z))
  (*add cheat tac focused on any subgoal of second goal cluster*)
  >>= with_state (cheat_tac RMD.promising #> add_tac amd P.LOW F.none)
  (*print the third action*)
  >>= (fn z => pretty_action z >>= arr Pretty.writeln >>= arr (K z))
  >>= top4 >>= Z1.ZM.Unzip.morph
  (*repeat best-first-search for 4 steps*)
  >>= repeat_fold_pactions_max_df (SOME 4)
  (*get the theorems*)
  >>= Z1.ZM.Zip.morph >>= with_state finish_gclusters_oldest_first >>= arr Seq.list_of
  ) |> MS.eval @{context} (*pass context to state monad*)
\<close>
oops

end
