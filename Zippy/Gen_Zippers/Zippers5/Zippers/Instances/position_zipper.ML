(*  Title:      Zippy/position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  (*list of x-positions from current position to the root; init=0, left=negative, right=positive*)
  type position = int L.t
  val init_x : int

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = unit
  where type @{AllT_args} ZD.content = position
end

functor \<^eval>\<open>sfx_T_nargs "Position_Zipper"\<close>(
    L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  ) : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close> =
struct

structure L = L
type position = int L.t
val init_x = 0

structure M = L.M
open M
structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves_List_Enumerable"\<close>(
    fun init_data _ = pure ()
    structure L = L
    structure E = \<^eval>\<open>sfx_T_nargs "Int_Enumerable"\<close>(
      structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(M)
      type @{AllT_args} init_data = unit
      fun first _ = pure init_x
    ))
  structure ZD = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Data"\<close>(
    type @{AllT_args} content = @{AllT_args} ZM.zipper))
open Z

end
