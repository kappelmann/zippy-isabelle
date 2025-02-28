\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy\<close>
theory Zippy_Base
  imports
    ML_Unification.ML_Logger
    ML_Unification.Setup_Result_Commands
begin

paragraph \<open>Summary\<close>
text \<open>Zippy is a theorem-proving framework based on zippers.\<close>

setup_result zippy_logger = \<open>Logger.new_logger Logger.root "Zippy"\<close>

end
