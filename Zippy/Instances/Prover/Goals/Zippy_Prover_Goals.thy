\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover_Goals
  imports
    ML_Union_Find
    ML_Unification.Unify_Resolve_Tactics_Base
    Zippy_Base
begin

paragraph \<open>Summary\<close>
text \<open>Goals for Zippy prover.\<close>

ML_file\<open>zippy_thm_state.ML\<close>
ML_file\<open>zippy_goal_clusters.ML\<close>
ML_file\<open>zippy_goal_cluster.ML\<close>
ML_file\<open>zippy_focus.ML\<close>

end
