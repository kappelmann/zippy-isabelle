\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance
  imports
    ML_Unification.ML_Priorities
    Zippy_Actions_Positions
    Zippy_Lists_Tactic
    Zippy_Runs
begin

ML_file\<open>zippy_instance.ML\<close>

ML\<open>
  @{functor_instance struct_name = Zippy
    and functor_name = Zippy_Instance
    and id = \<open>""\<close>
    and more_args = \<open>
      type prio = Prio.prio
      val prio_ord = Prio.ord #> rev_order
      val pretty_prio = Prio.pretty\<close>}
  structure Zippy = struct open Zippy; structure Prio = Prio end
\<close>

ML_file\<open>zippy_util.ML\<close>
ML\<open>structure Zippy = struct open Zippy; structure Util = Zippy_Util end\<close>

ML_file\<open>zippy_ztactic_util.ML\<close>
ML\<open>structure Zippy = struct open Zippy; structure Tac_Util = Zippy_ZTactic_Util end \<close>

end
