(*  Title:      HOCLP/position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "POSITION_ZIPPER"\<close> =
sig
  structure LI : GLIST
  (*list of x-positions from current position to the root; init=0, left=negative, right=positive*)
  type position = int LI.t
  val init_x : int

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZM.container = unit
  where type @{T_args} ZO.content = position
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Position_Zipper"\<close>(
    structure A : KLEISLI_ARROW_ARROW_APPLY
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.A.cat
    structure LI : GLIST
    sharing type LI.M.t = A.K.M.t
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "POSITION_ZIPPER"\<close> =
struct

structure LI = LI
type position = int LI.t
val init_x = 0

structure M = A.K.M
open M
structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves_List_Enumerable"\<close>(
    fun init_data _ = pure ()
    structure L = LI
    structure E = \<^eval>\<open>T_Args.suffix_Poly_nargs "Int_Enumerable"\<close>(
      structure M = Move_Base(M)
      type @{T_args} init_data = unit
      fun first _ = pure init_x
    ))
  structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper" ^ "_Optics"\<close>(
    structure A = A
    structure L = L
    type @{T_args} content = @{T_args} ZM.zipper))
open Z

end
