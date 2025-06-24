\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Goals_Base
  imports
    ML_Typeclasses.ML_Typeclasses_Base
    ML_Unification.Unify_Resolve_Tactics_Base
    ML_Union_Find
begin

ML_file\<open>zippy_thm_state.ML\<close>
ML_file\<open>zippy_goal_clusters.ML\<close>
ML_file\<open>zippy_goal_cluster.ML\<close>

ML_file\<open>zippy_goal_focus.ML\<close>

ML_file\<open>zippy_goal_results.ML\<close>

ML_file\<open>zippy_top_meta_vars.ML\<close>

end
