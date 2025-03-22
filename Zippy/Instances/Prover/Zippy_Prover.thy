\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover
  imports
    Gen_Zippy_Prover
    ML_Alternating_Zippers_Instances
    ML_Enumerable_Util
begin

paragraph \<open>Summary\<close>
text \<open>Zippy prover using list containers.\<close>

ML_file\<open>zippy_prover_base.ML\<close>
ML_file\<open>zippy_prover.ML\<close>

end
