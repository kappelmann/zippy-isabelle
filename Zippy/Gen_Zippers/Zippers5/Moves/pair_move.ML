(*  Title:      Zippy/pair_move.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_MOVE"\<close> =
sig
  structure M1 : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  structure M2 : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type M1.M.t = M2.M.t

  include \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  where type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
  where type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to
  sharing type M.t = M1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
    structure M1 : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    structure M2 : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    sharing type M2.M.t = M1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_MOVE"\<close>
  =
struct

structure M1 = M1
structure M2 = M2

structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = M1
open M

type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to

fun move x = x |> M1.*** (M1.move, M2.move)

end
