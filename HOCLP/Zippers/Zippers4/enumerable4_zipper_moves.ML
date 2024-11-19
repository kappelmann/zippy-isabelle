(*  Title:      HOCLP/enumerable4_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Zip.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor DFS_Postorder_Enumerable_Zipper4(
    structure AE : LAZY_ARROW_EXCEPTION_REC
    structure Z : ZIPPER4_MOVES
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AE.cat
  ) :
    LAST_ENUMERABLE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
  =
Last_Enumerable4(
  structure SC = Semi_Category(AE) open SC
  fun left_up_left _ = AE.catch' Z.Left.move (left_up_left o Z.Up.move)
    |> Lazy_Cat_Util.unlift
  structure E = Enumerable4(
    structure M = Z
    type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.container
    type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
    fun repeat_down _ = AE.repeat Z.Down.move ()
    fun first _ = (repeat_down o Z.Zip.move) ()
    fun next _ = AE.catch' (repeat_down o Z.Right.move) Z.Up.move
      |> Lazy_Cat_Util.unlift
    fun prev _ = AE.catch' (AE.repeat Z.Right.move o Z.Down.move) left_up_left
      |> Lazy_Cat_Util.unlift
  )
  val last = Z.Zip.move
)
