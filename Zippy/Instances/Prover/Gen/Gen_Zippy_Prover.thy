\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Gen_Zippy_Prover
  imports
    Zippy_Goals
    Zippy_Prover_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Theorem proving framework based on zippers.\<close>

ML_file\<open>zippy_result_data_data.ML\<close>

ML_file\<open>gen_zippy_prover_base.ML\<close>
ML_file\<open>gen_zippy_prover.ML\<close>

end
