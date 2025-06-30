\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Structured Lenses\<close>
theory ML_Structured_Lenses
  imports
    ML_Gen_Zippers_Setup
begin

ML_gen_file\<open>structured_lens.ML\<close>
ML_gen_file\<open>sstructured_lens.ML\<close>
ML_gen_file\<open>comp_structured_lens.ML\<close>
ML_gen_file\<open>modify_structured_lens.ML\<close>
ML_gen_file\<open>pair_structured_lens.ML\<close>

setup\<open>fn theory =>
let val nzippers = Config.get_global theory ML_Gen.nzippers_config + 1
in Context.theory_map (ML_Gen.setup_nzippers nzippers) theory end\<close>

text \<open>Note: we reload the ML files, just with different parameters.\<close>
ML_gen_file\<open>structured_lens.ML\<close>
ML_gen_file\<open>sstructured_lens.ML\<close>

setup\<open>fn theory =>
let val nzippers = Config.get_global theory ML_Gen.nzippers_config - 1
in Context.theory_map (ML_Gen.setup_nzippers nzippers) theory end\<close>

end