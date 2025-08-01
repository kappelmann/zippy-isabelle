\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Resolve_Action_Data
  imports
    Generic_Term_Index_Data
    Zippy_Instance
begin

(*ground polymorphic types since only ground types can be stored in the generic context.*)
setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_resolve_action_data_mixin_base.ML\<close>
ML_file\<open>zippy_resolve_action_data_mixin.ML\<close>
(*reset grounding*)
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
