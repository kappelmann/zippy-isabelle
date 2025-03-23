\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Linked Zippers\<close>
theory ML_Linked_Zippers
  imports
    ML_Zippers
begin

ML\<open>
  val mk_name = ML_Gen.mk_name
  val succ_mod_nzippers = ML_Gen.succ_mod_nzippers'
  val pred_mod_nzippers = ML_Gen.pred_mod_nzippers'
\<close>

ML_gen_file\<open>linked_zipper_moves.ML\<close>
ML_gen_file\<open>linked_zipper.ML\<close>

end