\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Moves\<close>
theory ML_Moves_Base
  imports
    ML_Typeclasses.ML_ICategories
    ML_Args_Antiquotations
    ML_Eval_Antiquotation
    ML_IMap_Antiquotation
begin

ML_file\<open>move_base.ML\<close>

ML\<open>
  @{functor_instance struct_name = Para_Type_Args_Antiquotations
    and functor_name = Args_Antiquotations
    and id = \<open>"ParaT"\<close>
    and more_args = \<open>val init_args = {
      args = SOME ["'p1"],
      sep = SOME ", ",
      encl = SOME ("", ""),
      encl_arg = SOME ("", ""),
      start = SOME 0,
      stop = SOME NONE
    }\<close>}
\<close>
local_setup \<open>Para_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set parameter type args antiquotation arguments")\<close>
setup \<open>Para_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>Para_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

ML\<open>
  @{functor_instance struct_name = Poly_Type_Args_Antiquotations
    and functor_name = Args_Antiquotations
    and id = \<open>"PolyT"\<close>
    and more_args = \<open>val init_args = {
      args = SOME ["'a1"],
      sep = SOME ", ",
      encl = SOME ("", ""),
      encl_arg = SOME ("", ""),
      start = SOME 0,
      stop = SOME NONE
    }\<close>}
\<close>
local_setup \<open>Poly_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set polymorphic type args antiquotation arguments")\<close>
setup \<open>Poly_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>Poly_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

ML\<open>
  @{functor_instance struct_name = Type_Args_Antiquotations
    and functor_name = Args_Antiquotations
    and id = \<open>"T"\<close>
    and more_args = \<open>val init_args = {
      args = SOME ["'p1", "'a1"],
      sep = SOME ", ",
      encl = SOME ("(", ")"),
      encl_arg = SOME ("", ""),
      start = SOME 0,
      stop = SOME NONE
    }\<close>}
\<close>
local_setup \<open>Type_Args_Antiquotations.setup_args_attribute
  (SOME "set type args antiquotation arguments")\<close>
setup \<open>Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>Type_Args_Antiquotations.setup_arg_antiquotation\<close>

ML_file\<open>t_args.ML\<close>

end