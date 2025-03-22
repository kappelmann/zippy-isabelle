(*  Title:      HOCLP/pair_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_MOVES"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  where type @{AllT_args} container = @{AllT_args} Z1.container * @{AllT_args} Z2.container
  where type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Moves"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    sharing type Z2.M.t = Z1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_MOVES"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

type @{AllT_args} container = @{AllT_args} Z1.container * @{AllT_args} Z2.container
type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper

structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = Z1
open M

structure Zip = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Zip; structure M2 = Z2.Zip)
structure Unzip = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Unzip; structure M2 = Z2.Unzip)
structure Up = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Up; structure M2 = Z2.Up)
structure Down = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Down; structure M2 = Z2.Down)
structure Left = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Left; structure M2 = Z2.Left)
structure Right = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Right; structure M2 = Z2.Right)

end

