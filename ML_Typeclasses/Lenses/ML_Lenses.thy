\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Lenses
  imports
    ML_ICategories
begin

ML_file\<open>lens.ML\<close>

(*standard function space lense*)
ML\<open>structure SLens = Lens(SArrow_Apply)\<close>

end