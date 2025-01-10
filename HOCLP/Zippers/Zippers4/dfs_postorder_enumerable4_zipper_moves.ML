(*  Title:      HOCLP/dfs_postorder_enumerable4_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Zip.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor DFS_Postorder_Enumerable4_Zipper_Moves(
    structure AE : KLEISLI_ARROW_EXCEPTION_REC
    structure Z : ZIPPER4_MOVES
    sharing type Z.M.t = AE.K.M.t
  ) :
    LAST_ENUMERABLE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
  =
Last_Enumerable4(
  structure SC = Semi_Category(AE) open SC
  fun left_up_left x = x |> AE.catch' Z.Left.move (Z.Up.move >>> left_up_left)
  structure E = Enumerable4(
    structure M = Z
    type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.container
    type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
    fun repeat_down x = x |> AE.repeat Z.Down.move
    fun first x = x |> (Z.Zip.move >>> repeat_down)
    fun next x = x |> AE.catch' (Z.Right.move >>> repeat_down) Z.Up.move
    fun prev x = x |> AE.catch' (Z.Down.move >>> AE.repeat Z.Right.move) left_up_left
  )
  val last = Z.Zip.move
)
