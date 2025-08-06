\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Resolve
  imports
    Generic_Term_Index_Data
    Zippy_Instance
begin

ML_file\<open>zippy_instance_resolve.ML\<close>
ML\<open>
local structure Zippy_Resolve = Zippy_Instance_Resolve(structure Z = Zippy; structure Ctxt = Z.Ctxt)
in structure Zippy = struct open Zippy Zippy_Resolve end end\<close>

(*ground polymorphic types since only ground types can be stored in the generic context.*)
setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_resolve_data.ML\<close>
(*reset grounding*)
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
