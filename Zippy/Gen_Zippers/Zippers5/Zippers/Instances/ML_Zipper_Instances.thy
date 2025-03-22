\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Zipper_Instances
  imports
    ML_Enumerable
    ML_Lists
    ML_Zippers
begin

ML_gen_file\<open>content_zipper.ML\<close>
ML_gen_file\<open>direction_zipper.ML\<close>

ML_gen_file\<open>dfs_postorder_enumerable_zipper_moves.ML\<close>

ML_gen_file\<open>zipper_moves_list_enumerable.ML\<close>
ML_gen_file\<open>position_zipper.ML\<close>

ML_gen_file\<open>list_zipper.ML\<close>
ML_gen_file\<open>rose_zipper.ML\<close>

end
