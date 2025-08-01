\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance
  imports
    ML_Unification.ML_Priorities
    Zippy_Actions_Positions
    Zippy_Lists_Goal_Pos_Updates
    Zippy_Runs
    Zippy_Tactics
begin

ML_file\<open>zippy_instance.ML\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: Zippy
  functor_name: Zippy_Instance
  id: \<open>"zippy"\<close>
  more_args: \<open>
    type prio = Prio.prio;
    val prio_ord = Prio.ord #> rev_order
    val pretty_prio = Prio.pretty\<close>\<close>
structure Zippy = struct open Zippy; structure Prio = Prio end
\<close>

ML_file\<open>zippy_instance_util.ML\<close>
ML\<open>structure Zippy = struct open Zippy; structure Util = Zippy_Instance_Util end\<close>
ML_file\<open>zippy_instance_ztactic_util.ML\<close>
ML\<open>structure Zippy = struct open Zippy; structure Tac_Util = Zippy_Instance_ZTactic_Util end\<close>

ML\<open>
structure ML_Gen =
struct
open ML_Gen
val ground_zipper_types =
  let val mk_groundT = K "unit"
  in ML_Gen.setup_zipper_args' (NONE, SOME mk_groundT) (NONE, SOME mk_groundT) end
val reset_zipper_types = ML_Gen.setup_zipper_args' (NONE, NONE) (NONE, NONE)
end
\<close>

end
