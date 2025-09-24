\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Classical
  imports
    HOL.HOL
    Zippy_Instance
begin

ML_file\<open>zippy_instance_classical.ML\<close>

ML\<open>
local structure Zippy_Classical = Zippy_Instance_Classical(structure Z = Zippy; structure Ctxt = Z.Ctxt)
in structure Zippy = struct open Zippy Zippy_Classical end end
\<close>

end
