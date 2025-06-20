\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Action_Clusters
  imports
    Zippy_Base
    SpecCheck.SpecCheck_Show
    Zippy_Identifiers
begin

ML_file\<open>zippy_copy_mixin_base.ML\<close>
ML_file\<open>zippy_copy_mixin.ML\<close>

ML_file\<open>zippy_enum_copy_mixin.ML\<close>

ML_file\<open>zippy_action_cluster_metadata.ML\<close>
ML_file\<open>zippy_action_cluster_metadata_mixin_base.ML\<close>

end
