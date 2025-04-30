\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Goals_Base
  imports
    ML_Unification.Unify_Resolve_Tactics_Base
    ML_Union_Find
begin

ML_file\<open>zippy_thm_state.ML\<close>
ML_file\<open>zippy_goal_clusters.ML\<close>
ML_file\<open>zippy_goal_cluster.ML\<close>
ML_file\<open>zippy_goal_focus.ML\<close>

end
