(*  Title:      Zippy/modify_zipper_moves_container.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Moves_Container"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    type @{AllT_args} ncontainer
    val ncontainer : (@{ParaT_args} @{AllT_args} Z.container, @{AllT_args} ncontainer) Z.move
    val dest_ncontainer : (@{ParaT_args} @{AllT_args} ncontainer, @{AllT_args} Z.container) Z.move
  )
  : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    where type @{AllT_args} container = @{AllT_args} ncontainer
    where type @{AllT_args} zipper = @{AllT_args} Z.zipper
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
  open Z
  structure M = Z
  type @{AllT_args} container = @{AllT_args} ncontainer
  structure Base = struct
    type @{AllT_args} nfrom = @{AllT_args} ncontainer
    type @{AllT_args} nto = @{AllT_args} ncontainer
    val dest_nfrom = dest_ncontainer
    val nto = ncontainer
  end
  structure Zip = \<^eval>\<open>sfx_T_nargs "Modify_Move_From"\<close>(
    open Base; structure M = Z.Zip)
  val zip = Zip.move
  structure Unzip = \<^eval>\<open>sfx_T_nargs "Modify_Move_To"\<close>(
    open Base; structure M = Z.Unzip)
  val unzip = Unzip.move
  val up = Z.Up.move
  val down = Z.Down.move
  val left = Z.Left.move
  val right = Z.Right.move
)
