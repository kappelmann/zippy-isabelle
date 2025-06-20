\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Runs
  imports
    Zippy_Actions
    Zippy_Lists_Goals
    Zippy_Lists_Positions
    Zippy_State
begin

ML_file\<open>zippy_runs_mixin_base.ML\<close>
ML_file\<open>zippy_runs_mixin.ML\<close>

ML_file\<open>zippy_lists_state_positions_mixin_base.ML\<close>
ML_file\<open>zippy_state_runs_mixin.ML\<close>

end
