\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Examples
  imports
    Zippy.Zippy_Prover_Instances
    Main
begin

text \<open>Some simple examples showcasing navigation in the zipper and the creation of theorems using
the best-first search instantiation from the paper.\<close>

ML\<open>
  (*syntax setup for monads and arrows*)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Zippy)
  structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(Zippy)
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(Zippy.M)
  open SC Zippy M

  (*halves the priorities at each pull of an action's result sequence*)
  fun halve_prio_co p = update_prio_co (fn _ => P.halve) p

  (*add a tactic action whose results' priorites are halved after each pull*)
  fun add_tac amd p focus tac z =
    amd >>= (fn amd => cons_move_tac amd (halve_prio_co p) tac focus z)

  (*tactic solving every goal*)
  fun cheat_tac prog ctxt = Skip_Proof.cheat_tac ctxt
    |> lift_all_goals_focus_tac (K (Zippy_Result_Metadata.metadata prog))
    T.single_goal_empty_target

  (*resolution with theorems*)
  fun zippy_resolve_tac prog thms ctxt = resolve_tac ctxt thms
    |> lift_every_goals_focus_tac (K (Zippy_Result_Metadata.metadata prog))
    T.single_goal_moved_target

  (*just some action metadata*)
  fun amd _ = AMD.metadata (@{binding "test action"}, "action description")
\<close>

text \<open>Figure 6 from the paper.

Exhaustively run all rules and apply as tactic. Of course, this is only to show how the zipper
works and not meant for production. When used in practice, one should return results as soon as
there are no more subgoals in one of the tree's branches.\<close>

lemma shows "A \<and> B" "C \<and> D"
apply (tactic \<open>fn state =>
  let
    val amd = amd ()
    val opt_statesq =
      (*initialise the zipper*)
      (init_state' mk_gcd_more state >>= arr snd
      (*add the conjunction tactic to the first goal cluster*)
      >>= Down1.move
      >>= with_state (zippy_resolve_tac RMD.promising @{thms conjI} #> add_tac amd P.HIGH (F.goals [1]))
      (*add the conjunction tactic to the second goal cluster*)
      >>= Up4.move >>= Up3.move >>= Z2.ZM.Down.move
      >>= with_state (zippy_resolve_tac RMD.promising @{thms conjI} #> add_tac amd P.HIGH (F.goals [1]))
      >>= top4 >>= Z1.ZM.Unzip.move
      (*repeat best-first-search until no more changes (instead of NONE, you can pass in SOME fuel); cf. below*)
      >>= repeat_fold_run_max_paction_dfs NONE
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
back
back
oops

declare [[ML_print_depth = 100]]

text \<open>Example with meta variable clusters, navigation, and printing.\<close>

schematic_goal shows "A \<and> ?B" "?B \<and> C" "D"
ML_val\<open>
val amd = amd ()
val state = @{Isar.goal} |> #goal
val opt_statesq =
  (*initialise the zipper*)
  (init_state' mk_gcd_more state >>= arr snd
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
  >>= repeat_fold_run_max_paction_dfs (SOME 4)
  (*get the theorems*)
  >>= Z1.ZM.Zip.move >>= with_state finish_gclusters_oldest_first >>= arr Seq.list_of
  ) |> MS.eval @{context} (*pass context to state monad*)
\<close>
oops

end
