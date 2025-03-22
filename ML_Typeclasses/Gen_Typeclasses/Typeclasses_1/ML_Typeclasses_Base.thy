\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Typeclasses_Base
  imports
    Gen_ML_Typeclasses_Base
    ML_Eval_Antiquotation
begin

declare [[ParaT_args args = ['p1] and sep = ", " and encl = "" ", " and encl_arg = "" "" and stop = ]]

ML\<open>
  val sfx_ParaT_nargs = ML_Gen.sfx_ParaT_nargs
\<close>

ML_gen_file\<open>typeclass_base.ML\<close>
ML_gen_file\<open>typeclass_base_instance.ML\<close>

end