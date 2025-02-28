(*  Title:      HOCLP/pair_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ZIPPER" ^ "_MOVES"\<close> =
sig
  structure Z1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
  structure Z2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
  where type @{T_args} container = @{T_args} Z1.container * @{T_args} Z2.container
  where type @{T_args} zipper = @{T_args} Z1.zipper * @{T_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper" ^ "_Moves"\<close>(
    structure Z1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    structure Z2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    sharing type Z2.M.t = Z1.M.t
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ZIPPER" ^ "_MOVES"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

type @{T_args} container = @{T_args} Z1.container * @{T_args} Z2.container
type @{T_args} zipper = @{T_args} Z1.zipper * @{T_args} Z2.zipper

structure M : MOVE_BASE = Z1
open M

structure Zip = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Zip; structure M2 = Z2.Zip)
structure Unzip = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Unzip; structure M2 = Z2.Unzip)
structure Up = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Up; structure M2 = Z2.Up)
structure Down = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Down; structure M2 = Z2.Down)
structure Left = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Left; structure M2 = Z2.Left)
structure Right = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = Z1.Right; structure M2 = Z2.Right)

end

