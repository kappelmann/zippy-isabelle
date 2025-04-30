(*  Title:      Zippy/move_base.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> =
sig
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY_BASE"\<close>
  sharing type K.M.t = M.t
  type (@{ParaT_args} 'a, 'b) move = (@{ParaT_args} 'a, 'b) cat
  type (@{ParaT_args} 'a) hom_move = (@{ParaT_args} 'a, 'a) move
end

functor \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> =
struct
structure Min = M
structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(M)
open K
structure M = Min
type (@{ParaT_args} 'a, 'b) move = (@{ParaT_args} 'a, 'b) cat
type (@{ParaT_args} 'a) hom_move = (@{ParaT_args} 'a, 'a) move
end
