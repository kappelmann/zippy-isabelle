(*  Title:      Zippy/zippy_state_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_STATE_MIXIN_BASE =
sig
  structure MS : \<^eval>\<open>sfx_ParaT_nargs "ISTATE_TRANS"\<close>
  include ZIPPY_BASE_BASE
  where type (@{ParaT_args} 'a) M.t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) MS.t
end

functor Zippy_State_Mixin_Base(A :
  sig
    structure MS : \<^eval>\<open>sfx_ParaT_nargs "ISTATE_TRANS"\<close>
    include ZIPPY_BASE_BASE
    where type (@{ParaT_args} 'a) M.t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) MS.t
  end
  ) : ZIPPY_STATE_MIXIN_BASE
  = A