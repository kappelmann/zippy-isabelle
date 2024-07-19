(*  Title:      HOCLP/bi_enumerable_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Init.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor DFS_Postorder_Enumerable_Bi_Zipper(
    structure ME : IMONAD_EXCEPTION_BASE
    structure Z : BI_ZIPPER
    sharing type ME.t = Z.K.M.t)
  :
    LAST_BI_ENUMERABLE
    where type ('i, 'a, 'b) init_data = ('i, 'a, 'b) Z.Init.from
    where type ('i, 'a, 'b) data = ('i, 'a, 'b) Z.data
  =
Last_Bi_Enumerable(
  structure MU = Move_Util(ME)
  open MU MU.C
  fun left_up_left x = x |> AE.catch' Z.Left.move (left_up_left o Z.Up.move)
  structure E = Bi_Enumerable(
    structure M = Z
    type ('i, 'a, 'b) init_data = ('i, 'a, 'b) Z.Init.from
    type ('i, 'a, 'b) data = ('i, 'a, 'b) Z.data
    fun repeat_down x = x |> AE.repeat Z.Down.move
    fun first x = x |> repeat_down o Z.Init.move
    fun next x = x |> AE.catch' (repeat_down o Z.Right.move) Z.Up.move
    fun prev x = x |> AE.catch' (AE.repeat Z.Right.move o Z.Down.move) left_up_left
  )
  fun last x = x |> Z.Init.move
)
