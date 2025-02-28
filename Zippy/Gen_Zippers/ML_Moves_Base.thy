\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Moves\<close>
theory ML_Moves_Base
  imports
    ML_Typeclasses.ML_ICategories
    ML_Args_Antiquotations
    ML_Eval_Antiquotation
    ML_IMap_Antiquotation
    keywords "ML_file'" :: thy_decl
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

text \<open>Setup alternative @{command ML_file} command to avoid errors when loading files twice.
This is needed since we provide ML files whose source depends on context variables and that should
be loadable in different contexts.\<close>

ML\<open>
  let
    (*adapted from Pure/ML/ml_file.ML (removed duplicated file-loading check by skipping "provide")*)
    fun command environment catch_all debug get_file = Toplevel.generic_theory (fn gthy =>
      let
        val file = get_file (Context.theory_of gthy)
        (* val provide = Resources.provide_file file; *)
        val source = Token.file_source file

        val _ = Document_Output.check_comments (Context.proof_of gthy) (Input.source_explode source)

        val flags: ML_Compiler.flags =
          {environment = environment, redirect = true, verbose = true, catch_all = catch_all,
            debug = debug, writeln = writeln, warning = warning}
      in
        gthy
        |> Local_Theory.touch_ml_env
        |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
        |> Local_Theory.propagate_ml_env
        (* |> Context.mapping provide (Local_Theory.background_theory provide) *)
      end)
    val ML = command "" false
  in
    Outer_Syntax.command \<^command_keyword>\<open>ML_file'\<close> "read and evaluate Isabelle/ML file without duplication check."
      (Resources.parse_file --| Scan.option \<^keyword>\<open>;\<close> >> ML NONE)
  end
\<close>

end