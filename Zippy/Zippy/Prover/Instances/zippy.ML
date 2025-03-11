(*  Title:      HOCLP/zippy.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY =
sig
  include ZIPPY_PROVER_INSTANCE
end

structure Zippy : ZIPPY =
struct

structure Z = Zippy_Prover_Instance(Zippy_Prover_Instance_Base(
  Monad_Exception_Monad_Or(Option_Monad_Or_Trans(Identity_Monad))))
open Z

end
