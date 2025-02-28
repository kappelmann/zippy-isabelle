(*  Title:      HOCLP/pair_move.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_MOVE"\<close> =
sig
  structure M1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  structure M2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type M1.M.t = M2.M.t

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  where type @{T_args} from = @{T_args} M1.from * @{T_args} M2.from
  where type @{T_args} to = @{T_args} M1.to * @{T_args} M2.to
  sharing type M1.M.t = M.t
  sharing type M2.M.t = M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
    structure M1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    structure M2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    sharing type M2.M.t = M1.M.t
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_MOVE"\<close>
  =
struct

structure M1 = M1
structure M2 = M2

structure M : MOVE_BASE = M1
open M

type @{T_args} from = @{T_args} M1.from * @{T_args} M2.from
type @{T_args} to = @{T_args} M1.to * @{T_args} M2.to

fun move x = x |> M1.*** (M1.move, M2.move)

end
