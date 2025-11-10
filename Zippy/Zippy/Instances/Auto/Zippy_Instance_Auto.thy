\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy Auto (zippy)\<close>
theory Zippy_Instance_Auto
  imports
    Extended_Simp_Data
    Zippy_Instance_Resolve
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_auto.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end