\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generic Zippers Setup\<close>
theory ML_Gen_Zippers_Setup
  imports
    ML_Gen_Zippers_Base
    ML_IMap_Antiquotation
    ML_Typeclasses.ML_Lenses
begin

ML\<open>
structure ML_Gen =
struct
open ML_Gen
fun setup_nzippers nzippers context =
  let
    val zipperT_args = map_range (General_Util.succ #> string_of_int #> prefix "'a") nzippers
    val paraT_args = Para_Type_Args_Antiquotations.get_args context
  in
    context
    |> Config.put_generic ML_Gen.nzippers_config nzippers
    |> ML_Gen.ZipperT.map_args (K zipperT_args)
    |> ML_Gen.AllT.map_args (K (paraT_args @ zipperT_args))
    |> Standard_IMap_Antiquotation.map_stop (K nzippers)
  end
end
\<close>

declare [[ParaT_args sep = ", " and encl = "" ", " and encl_arg = "" "" and stop = ]]
and [[ZipperT_args sep = ", " and encl = "" "" and encl_arg = "" "" and stop = ]]
and [[AllT_args sep = ", " and encl = "(" ")" and encl_arg = "" "" and stop = ]]
and [[imap start = 1]]
(*setup for 5-alternating zippers*)
setup\<open>Context.theory_map (ML_Gen.setup_nzippers 5)\<close>

ML\<open>
  val sfx_ParaT_nargs = ML_Gen.sfx_ParaT_nargs
  val sfx_T_nargs = ML_Gen.sfx_T_nargs
  val sfx_inst_T_nargs = ML_Gen.sfx_inst_T_nargs
\<close>

end