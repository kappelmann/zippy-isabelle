\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Tactics
  imports
    Zippy_Actions
    Zippy_Action_Clusters
    Zippy_Goals
    Zippy_Tactics_Base
begin

ML_file\<open>zippy_goals_tactic_mixin_base.ML\<close>

ML_file\<open>zippy_goals_tactic_copy_mixin_base.ML\<close>
ML_file\<open>zippy_goals_tactic_copy_mixin.ML\<close>

ML_file\<open>zippy_goals_tactic_copy_paction_mixin_base.ML\<close>

ML_file\<open>zippy_tactic_result_progress.ML\<close>
ML_file\<open>zippy_tactic_result_metadata.ML\<close>
ML_file\<open>zippy_tactic_result_metadata_mixin_base.ML\<close>
ML_file\<open>zippy_tactic_result_metadata_mixin.ML\<close>

end
