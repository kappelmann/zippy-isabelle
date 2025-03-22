\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Moves
  imports
    ML_Gen_Zippers_Base
    ML_IMap_Antiquotation
begin

declare [[nzippers = 5]]
declare [[ParaT_args args = ['p1]]]
declare [[ZipperT_args args = ['a1, 'a2, 'a3, 'a4, 'a5] and sep = ", " and encl = "" ""
  and encl_arg = "" "" and stop = ]]
declare [[AllT_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5] and sep = ", " and encl = "(" ")"
  and encl_arg = "" "" and stop = ]]
declare [[imap start = 1 and stop = 5]]

ML\<open>
  val sfx_ParaT_nargs = ML_Gen.sfx_ParaT_nargs
  val sfx_T_nargs = ML_Gen.sfx_T_nargs
\<close>

ML_gen_file\<open>move_base.ML\<close>
ML_gen_file\<open>move.ML\<close>

ML_gen_file\<open>pair_move.ML\<close>
ML_gen_file\<open>replace_move_from_to.ML\<close>

end