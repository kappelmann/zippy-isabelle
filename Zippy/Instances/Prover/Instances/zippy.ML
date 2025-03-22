(*  Title:      Zippy/zippy.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY =
sig
  include ZIPPY_PROVER_INSTANCE
end

structure Zippy : ZIPPY =
struct

structure Z = Zippy_Prover_Instance(Zippy_Prover_Instance_Base(
  \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))))
open Z

end
