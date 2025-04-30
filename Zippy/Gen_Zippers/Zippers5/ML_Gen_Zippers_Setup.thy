\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generic Zippers Setup\<close>
theory ML_Gen_Zippers_Setup
  imports
    ML_Gen_Zippers_Base
    ML_IMap_Antiquotation
begin

declare [[nzippers = 5]]
declare [[ParaT_args args = ['p1] and sep = ", " and encl = "" ", "
  and encl_arg = "" "" and stop = ]]
declare [[ZipperT_args args = ['a1, 'a2, 'a3, 'a4, 'a5] and sep = ", " and encl = "" ""
  and encl_arg = "" "" and stop = ]]
declare [[AllT_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5] and sep = ", " and encl = "(" ")"
  and encl_arg = "" "" and stop = ]]
declare [[imap start = 1 and stop = 5]]

ML\<open>
  val sfx_ParaT_nargs = ML_Gen.sfx_ParaT_nargs
  val sfx_T_nargs = ML_Gen.sfx_T_nargs
  val sfx_inst_T_nargs = ML_Gen.sfx_inst_T_nargs
\<close>

end