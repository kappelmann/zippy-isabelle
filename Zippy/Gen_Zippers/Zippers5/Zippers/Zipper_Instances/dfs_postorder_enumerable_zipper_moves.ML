(*  Title:      HOCLP/dfs_postorder_enumerable_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Zip.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    structure AE : KLEISLI_ARROW_EXCEPTION_REC
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    sharing type Z.M.t = AE.K.M.t
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "LAST_ENUMERABLE"\<close>
    where type @{T_args} init_data = @{T_args} Z.container
    where type @{T_args} data = @{T_args} Z.zipper
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Last_Enumerable"\<close>(
  structure SC = Semi_Category(AE) open SC
  fun left_up_left x = x |> AE.catch' Z.Left.move (Z.Up.move >>> left_up_left)
  structure E = \<^eval>\<open>T_Args.suffix_Poly_nargs "Enumerable"\<close>(
    structure M = Z
    type @{T_args} init_data = @{T_args} Z.container
    type @{T_args} data = @{T_args} Z.zipper
    fun repeat_down x = x |> AE.repeat Z.Down.move
    fun first x = x |> (Z.Zip.move >>> repeat_down)
    fun next x = x |> AE.catch' (Z.Right.move >>> repeat_down) Z.Up.move
    fun prev x = x |> AE.catch' (Z.Down.move >>> AE.repeat Z.Right.move) left_up_left
  )
  val last = Z.Zip.move
)
