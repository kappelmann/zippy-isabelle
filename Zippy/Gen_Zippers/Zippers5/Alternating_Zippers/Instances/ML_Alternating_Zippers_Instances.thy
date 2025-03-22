\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Alternating_Zippers_Instances
  imports
    ML_Alternating_Zippers
    ML_Zipper_Instances
begin

ML_gen_file\<open>alternating_position_zipper.ML\<close>
ML_gen_file\<open>alternating_depth_zipper.ML\<close>

ML_gen_file\<open>dfs_postorder_enumerable_alternating_zipper.ML\<close>

end
