\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Moves
  imports
    ML_Moves_Base
begin

declare [[ParaT_args args = ['p1] and sep = ", " and encl = "" "" and encl_arg = "" "" and stop = ]]
declare [[PolyT_args args = ['a1, 'a2, 'a3, 'a4, 'a5] and sep = ", " and encl = "" ""
  and encl_arg = "" "" and stop = ]]
declare [[T_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5] and sep = ", " and encl = "(" ")"
  and encl_arg = "" "" and stop = ]]
declare [[imap start = 1 and stop = 5]]

ML_file\<open>move.ML\<close>
ML_file\<open>pair_move.ML\<close>
ML_file\<open>replace_move_from_to.ML\<close>

end