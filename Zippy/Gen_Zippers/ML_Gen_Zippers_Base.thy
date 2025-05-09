\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generic Zippers Base Setup\<close>
theory ML_Gen_Zippers_Base
  imports
    Zippy_Base_Setup
    ML_Typeclasses.ML_Lenses
begin

text\<open>The ML code is parametrised by the number of zippers \<open>nzippers\<close>, the number of type parameters
of the underlying typeclasses \<open>'p1,...,'pn\<close>, and the number of additional type parameters for the
zipper \<open>'a1,...,'am\<close>.  All parameters of the underlying typeclasses are also put into the zipper
type per default since zippers for search trees must be able to store moves in the zipper
themselves, i.e. a zipper takes type parameters \<open>'p1,...,'pn,'a1,...,'am\<close>.

Note: due to a performance problem in Poly/ML's type checker, instantiation functors need to be
carefully used (i.e. avoid deep type instantiation chains):
\<^url>\<open>https://github.com/polyml/polyml/issues/213\<close>\<close>

ML\<open>
  @{functor_instance struct_name = Zipper_Type_Args_Antiquotations
    and functor_name = Args_Antiquotations
    and id = \<open>"ZipperT"\<close>
    and more_args = \<open>val init_args = {
      args = SOME ["'a1"],
      sep = SOME ", ",
      encl = SOME ("", ""),
      encl_arg = SOME ("", ""),
      start = SOME 0,
      stop = SOME NONE
    }\<close>}
\<close>
local_setup \<open>Zipper_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set zipper type args antiquotation arguments")\<close>
setup \<open>Zipper_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>Zipper_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

ML\<open>
  @{functor_instance struct_name = All_Type_Args_Antiquotations
    and functor_name = Args_Antiquotations
    and id = \<open>"AllT"\<close>
    and more_args = \<open>val init_args = {
      args = SOME ["'p1", "'a1"],
      sep = SOME ", ",
      encl = SOME ("(", ")"),
      encl_arg = SOME ("", ""),
      start = SOME 0,
      stop = SOME NONE
    }\<close>}
\<close>
local_setup \<open>All_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set all type args antiquotation arguments")\<close>
setup \<open>All_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>All_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

(*functions to create type generic ML code*)
ML\<open>
structure ML_Gen =
struct
  open ML_Gen
  structure ZipperT = Zipper_Type_Args_Antiquotations
  structure AllT = All_Type_Args_Antiquotations
  val nzippers_config = Attrib.setup_config_int @{binding "nzippers"} (K 0)
  fun nzippers _ = Config.get_generic (Context.the_generic_context ()) nzippers_config
  val nzippers' = nzippers #> string_of_int

  (*ML structure names may not begin with a digit; hence we add a "n" prefix*)
  val nprefix = prefix "n"
  fun pfx_nzippers s = mk_name [nprefix (nzippers' ()), s]

  (*modular arithmetic for domain [1,...,nzippers]*)
  fun succ_mod_nzippers i = (i mod nzippers ()) + 1
  fun pred_mod_nzippers i = ((i - 2) mod nzippers ()) + 1
  val succ_mod_nzippers' = succ_mod_nzippers #> string_of_int
  val pred_mod_nzippers' = pred_mod_nzippers #> string_of_int

  val ZipperT_nargs = Context.the_generic_context #> ZipperT.nargs
  val ZipperT_nargs' = ZipperT_nargs #> string_of_int
  fun sfx_T_nargs s = mk_name [s, ParaT_nargs (), ZipperT_nargs' ()]

  val pfx_sfx_nargs = pfx_nzippers #> sfx_T_nargs

  (*instantiate a zipper type*)
  fun sfx_inst s i = mk_name [s, string_of_int i]

  fun sfx_inst_T_nargs s = sfx_inst s #> sfx_T_nargs
  val pfx_sfx_inst_nargs = pfx_nzippers #> sfx_inst_T_nargs

  fun inst_zipperT instT i =
    let val ctxt = Context.the_local_context ()
    in
      1 upto ZipperT_nargs ()
      |> map (fn j => if i = j then instT else ZipperT.mk_arg_code (j - 1) ctxt)
      |> commas
    end

  fun AllT_args _ = AllT.mk_args_code (Context.the_local_context ())
end
\<close>

end