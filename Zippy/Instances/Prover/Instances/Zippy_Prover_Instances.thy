\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover_Instances
  imports
    ML_Typeclasses.ML_State
    ML_Unification.ML_Priorities
    Zippy_Prover_Action_Metadata
    Zippy_Prover_Action_Cluster_Metadata
    Zippy_Prover_Goal_Clusters_Metadata
    Zippy_Prover_Metadata_Data
    Zippy_Prover_Position
    Zippy_Prover_Result_Metadata
begin

paragraph \<open>Summary\<close>
text \<open>The standard Zippy prover instance, using a state monad.\<close>

ML_file\<open>zippy_prover_instance_base.ML\<close>
ML_file\<open>zippy_prover_instance.ML\<close>

ML_file\<open>zippy.ML\<close>

end
