(*  Title:      Zippy/move.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "MOVE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} from
  type @{AllT_args} to
  val move : (@{ParaT_args} @{AllT_args} from, @{AllT_args} to) move
end

signature \<^eval>\<open>sfx_T_nargs "HOM_MOVE"\<close> =
sig
  include \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type from = to
end

functor \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    type @{AllT_args} data
    val move : (@{ParaT_args} @{AllT_args} data) M.hom_move
  ) : \<^eval>\<open>sfx_T_nargs "HOM_MOVE"\<close> =
struct
open M
type @{AllT_args} from = @{AllT_args} data
type @{AllT_args} to = @{AllT_args} data
val move = move
end
