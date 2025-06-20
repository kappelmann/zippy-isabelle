\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Tactics_Base
  imports
    ML_Typeclasses.ML_Categories
    Zippy_Goals_Base
begin

paragraph \<open>Summary\<close>
text \<open>Tactics for Zippy prover.\<close>

ML_file\<open>zippy_goal_pos_update.ML\<close>
ML_file\<open>zippy_goal_pos_update_util.ML\<close>

ML_file\<open>zippy_rtactic_result.ML\<close>
ML_file\<open>zippy_rtactic.ML\<close>

ML_file\<open>zippy_ztactic_result.ML\<close>
ML_file\<open>zippy_ztactic_result_util.ML\<close>
ML_file\<open>zippy_ztactic.ML\<close>

end
