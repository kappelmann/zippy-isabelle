(*  Title:      HOCLP/replace_zipper_moves_container.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper_Moves_Container(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    type @{T_args} ncontainer
    val ncontainer : (@{ParaT_args}, @{T_args} Z.container, @{T_args} ncontainer) Z.move
    val dest_ncontainer : (@{ParaT_args}, @{T_args} ncontainer, @{T_args} Z.container) Z.move
  )
  : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    where type @{T_args} container = @{T_args} ncontainer
    where type @{T_args} zipper = @{T_args} Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  open Z
  structure M = Z
  type @{T_args} container = @{T_args} ncontainer
  structure Base = struct
    type @{T_args} nfrom = @{T_args} ncontainer
    type @{T_args} nto = @{T_args} ncontainer
    val dest_nfrom = dest_ncontainer
    val nto = ncontainer
  end
  structure Zip = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From"\<close>(
    open Base; structure M = Z.Zip)
  val zip = Zip.move
  structure Unzip = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_To"\<close>(
    open Base; structure M = Z.Unzip)
  val unzip = Unzip.move
  val up = Z.Up.move
  val down = Z.Down.move
  val left = Z.Left.move
  val right = Z.Right.move
)
