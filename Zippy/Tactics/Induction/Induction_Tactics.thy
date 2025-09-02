\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Induction_Tactics
  imports
    ML_Unification.ML_Tactic_Utils
    Zippy_ML_Tactic_Utils
    HOL.HOL
begin

ML_file\<open>induction_tactic.ML\<close>

ML\<open>structure Induction_Tactic_HOL = Induction_Tactic(Induct)\<close>

end