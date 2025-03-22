(*  Title:      Zippy/replace_zipper_moves_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Moves_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    type @{AllT_args} nzipper
    val nzipper : (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} nzipper) Z.move
    val dest_nzipper : (@{ParaT_args} @{AllT_args} nzipper, @{AllT_args} Z.zipper) Z.move
  )
  : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    where type @{AllT_args} container = @{AllT_args} Z.container
    where type @{AllT_args} zipper = @{AllT_args} nzipper
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
  open Z
  structure M = Z
  type @{AllT_args} zipper = @{AllT_args} nzipper
  structure Base =
  struct
    type @{AllT_args} nfrom = @{AllT_args} nzipper
    type @{AllT_args} nto = @{AllT_args} nzipper
    val dest_nfrom = dest_nzipper
    val nto = nzipper
  end
  structure Zip = \<^eval>\<open>sfx_T_nargs "Replace_Move_To"\<close>(
    open Base; structure M = Z.Zip)
  val zip = Zip.move
  structure Unzip = \<^eval>\<open>sfx_T_nargs "Replace_Move_From"\<close>(
    open Base; structure M = Z.Unzip)
  val unzip = Unzip.move
  structure Up = \<^eval>\<open>sfx_T_nargs "Replace_Move_From_To"\<close>(
    open Base; structure M = Z.Up)
  val up = Up.move
  structure Down = \<^eval>\<open>sfx_T_nargs "Replace_Move_From_To"\<close>(
    open Base; structure M = Z.Down)
  val down = Down.move
  structure Left = \<^eval>\<open>sfx_T_nargs "Replace_Move_From_To"\<close>(
    open Base; structure M = Z.Left)
  val left = Left.move
  structure Right = \<^eval>\<open>sfx_T_nargs "Replace_Move_From_To"\<close>(
    open Base; structure M = Z.Right)
  val right = Right.move
)