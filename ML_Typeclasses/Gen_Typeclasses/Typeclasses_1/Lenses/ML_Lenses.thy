\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Lenses
  imports
    ML_ICategories
begin

ML_gen_file\<open>lens.ML\<close>

(*standard function space lense*)
ML\<open>structure \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close> = \<^eval>\<open>sfx_ParaT_nargs "Lens"\<close>(
    structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens_Base"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Arrow_Apply"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>))
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(\<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>)
  )\<close>

end