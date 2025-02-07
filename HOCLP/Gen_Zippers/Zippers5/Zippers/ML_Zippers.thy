\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippers\<close>
theory ML_Zippers
  imports
    ML_Moves
    ML_Zippers_Base
begin

ML_file\<open>zipper_moves.ML\<close>
ML_file\<open>replace_zipper_moves_zipper.ML\<close>
ML_file\<open>replace_zipper_moves_container.ML\<close>
ML_file\<open>pair_zipper_moves.ML\<close>

ML_file\<open>zipper_optics.ML\<close>
ML_file\<open>replace_zipper_optics_zipper.ML\<close>
ML_file\<open>replace_zipper_optics_content.ML\<close>
ML_file\<open>pair_zipper_optics.ML\<close>

ML_file\<open>zipper_data.ML\<close>
ML_file\<open>zipper_optics_zipper_data.ML\<close>

ML_file\<open>zipper.ML\<close>
ML_file\<open>replace_zipper_zipper.ML\<close>
ML_file\<open>replace_zipper_content.ML\<close>
ML_file\<open>extend_zipper_context.ML\<close>
ML_file\<open>pair_zipper.ML\<close>

end