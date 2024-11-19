\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy\<close>
theory Zippy_Base
  imports
    ML_Unification.Setup_Result_Commands
    ML_Unification.Unify_Resolve_Tactics_Base
    ML_Coroutines
    ML_Union_Find
begin

paragraph \<open>Summary\<close>
text \<open>Zippy is a theorem-proving framework based on zippers.\<close>

setup_result zippy_logger = \<open>Logger.new_logger Logger.root "zippy"\<close>

ML_file\<open>zippy_thm_state.ML\<close>

ML_file\<open>zippy_goal_clusters.ML\<close>
ML_file\<open>zippy_goal_cluster.ML\<close>
ML_file\<open>zippy_action_cluster.ML\<close>
ML_file\<open>zippy_action.ML\<close>

ML_file\<open>zippy_action_util.ML\<close>

ML_file\<open>zippy_focus_pos.ML\<close>

end
