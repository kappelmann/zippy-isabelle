(*  Title:      HOCLP/replace_zipper_moves_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Moves_Zipper"\<close>(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    type @{T_args} nzipper
    val nzipper : (@{ParaT_args}, @{T_args} Z.zipper, @{T_args} nzipper) Z.move
    val dest_nzipper : (@{ParaT_args}, @{T_args} nzipper, @{T_args} Z.zipper) Z.move
  )
  : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    where type @{T_args} container = @{T_args} Z.container
    where type @{T_args} zipper = @{T_args} nzipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  open Z
  structure M = Z
  type @{T_args} zipper = @{T_args} nzipper
  structure Base =
  struct
    type @{T_args} nfrom = @{T_args} nzipper
    type @{T_args} nto = @{T_args} nzipper
    val dest_nfrom = dest_nzipper
    val nto = nzipper
  end
  structure Zip = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_To"\<close>(
    open Base; structure M = Z.Zip)
  val zip = Zip.move
  structure Unzip = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From"\<close>(
    open Base; structure M = Z.Unzip)
  val unzip = Unzip.move
  structure Up = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
    open Base; structure M = Z.Up)
  val up = Up.move
  structure Down = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
    open Base; structure M = Z.Down)
  val down = Down.move
  structure Left = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
    open Base; structure M = Z.Left)
  val left = Left.move
  structure Right = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
    open Base; structure M = Z.Right)
  val right = Right.move
)