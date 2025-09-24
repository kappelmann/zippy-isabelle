\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Simp
  imports
    Zippy_Instance
begin

ML_file\<open>zippy_instance_simp.ML\<close>

ML\<open>
local structure Zippy_Simp = Zippy_Instance_Simp(structure Z = Zippy; structure Ctxt = Z.Ctxt)
in structure Zippy = struct open Zippy Zippy_Simp end end
\<close>

end
