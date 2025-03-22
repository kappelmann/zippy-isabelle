(*  Title:      HOCLP/dfs_postorder_enumerable_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Zip.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor \<^eval>\<open>sfx_T_nargs "DFS_Postorder_Enumerable_Zipper_Moves"\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    sharing type Z.M.t = AE.K.M.t
  ) :
    \<^eval>\<open>sfx_T_nargs "LAST_ENUMERABLE"\<close>
    where type @{AllT_args} init_data = @{AllT_args} Z.container
    where type @{AllT_args} data = @{AllT_args} Z.zipper
  =
\<^eval>\<open>sfx_T_nargs "Last_Enumerable"\<close>(
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE) open SC
  fun left_up_left x = x |> AE.catch' Z.Left.move (Z.Up.move >>> left_up_left)
  structure E = \<^eval>\<open>sfx_T_nargs "Enumerable"\<close>(
    structure M = Z
    type @{AllT_args} init_data = @{AllT_args} Z.container
    type @{AllT_args} data = @{AllT_args} Z.zipper
    fun repeat_down x = x |> AE.repeat Z.Down.move
    fun first x = x |> (Z.Zip.move >>> repeat_down)
    fun next x = x |> AE.catch' (Z.Right.move >>> repeat_down) Z.Up.move
    fun prev x = x |> AE.catch' (Z.Down.move >>> AE.repeat Z.Right.move) left_up_left
  )
  val last = Z.Zip.move
)
