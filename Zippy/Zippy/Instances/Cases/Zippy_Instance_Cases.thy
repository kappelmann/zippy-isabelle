\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Cases
  imports
    (* Cases_Tactics *)
    Zippy_Instance
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_cases_data.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
