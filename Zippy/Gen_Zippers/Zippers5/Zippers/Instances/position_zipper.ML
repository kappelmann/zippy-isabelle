(*  Title:      HOCLP/position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close> =
sig
  structure LI : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  (*list of x-positions from current position to the root; init=0, left=negative, right=positive*)
  type position = int LI.t
  val init_x : int

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = unit
  where type @{AllT_args} ZO.content = position
end

functor \<^eval>\<open>sfx_T_nargs "Position_Zipper"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ARROW_APPLY"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) A.A.cat
    structure LI : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
    sharing type LI.M.t = A.K.M.t
  ) : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close> =
struct

structure LI = LI
type position = int LI.t
val init_x = 0

structure M = A.K.M
open M
structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves_List_Enumerable"\<close>(
    fun init_data _ = pure ()
    structure L = LI
    structure E = \<^eval>\<open>sfx_T_nargs "Int_Enumerable"\<close>(
      structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(M)
      type @{AllT_args} init_data = unit
      fun first _ = pure init_x
    ))
  structure ZO = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Optics"\<close>(
    structure A = A
    structure L = L
    type @{AllT_args} content = @{AllT_args} ZM.zipper))
open Z

end
