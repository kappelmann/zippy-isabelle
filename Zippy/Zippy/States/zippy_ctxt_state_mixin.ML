(*  Title:      Zippy/zippy_ctxt_state_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CTXT_STATE_MIXIN =
sig
  include ZIPPY_CTXT_STATE_MIXIN_BASE
  structure AS : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_STATE"\<close>
  sharing type AS.K.M.t = MS.t

  val with_ctxt : (Proof.context -> (@{ParaT_args} 'a, 'b) cat) -> (@{ParaT_args} 'a, 'b) cat
end

functor Zippy_Ctxt_State_Mixin(
    Ctxt : ZIPPY_CTXT_STATE_MIXIN_BASE
  ) : ZIPPY_CTXT_STATE_MIXIN =
struct
open Ctxt
structure AS = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_State"\<close>(MS)

fun with_ctxt f = AS.access (fn (x, s) => f s x)

end
