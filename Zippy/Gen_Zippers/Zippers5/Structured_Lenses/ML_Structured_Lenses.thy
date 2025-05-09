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

context
  (*FIXME: could be made generic with ML programming*)
  notes [[AllT_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
  and [[ZipperT_args args = ['a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
begin
text \<open>Note: we reload the ML files, just with different parameters.\<close>
ML_gen_file\<open>structured_lens.ML\<close>
ML_gen_file\<open>sstructured_lens.ML\<close>
end

end