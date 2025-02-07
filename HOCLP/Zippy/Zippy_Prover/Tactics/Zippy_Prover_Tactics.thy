\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover_Tactics
  imports
    ML_Typeclasses.ML_Lenses
    Zippy_Prover_Goals
begin

paragraph \<open>Summary\<close>
text \<open>Tactics for Zippy prover.\<close>

ML_file\<open>zippy_goal_pos_update.ML\<close>
ML_file\<open>zippy_goal_pos_update_util.ML\<close>

ML_file\<open>zippy_result_update_data.ML\<close>
ML_file\<open>zippy_tactic_result.ML\<close>
ML_file\<open>zippy_tactic.ML\<close>

end
