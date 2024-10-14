(*  Title:      HOCLP/bi_enumerable_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Init.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor DFS_Postorder_Enumerable_Bi_Zipper(
    structure AE : LAZY_IARROW_EXCEPTION
    structure Z : BI_ZIPPER
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.T.lcat
  ) :
    LAST_BI_ENUMERABLE
    where type ('i, 'a, 'b) init_data = ('i, 'a, 'b) Z.Init.from
    where type ('i, 'a, 'b) data = ('i, 'a, 'b) Z.data
  =
Last_Bi_Enumerable(
  structure SC = ISemi_Category(AE) open SC
  fun left_up_left _ = AE.catch' Z.Left.move (left_up_left o Z.Up.move) ()
  structure E = Bi_Enumerable(
    structure M = Z
    type ('i, 'a, 'b) init_data = ('i, 'a, 'b) Z.Init.from
    type ('i, 'a, 'b) data = ('i, 'a, 'b) Z.data
    fun repeat_down _ = AE.repeat Z.Down.move ()
    fun first _ = (repeat_down o Z.Init.move) ()
    fun next _ = AE.catch' (repeat_down o Z.Right.move) Z.Up.move ()
    fun prev _ = AE.catch' (AE.repeat Z.Right.move o Z.Down.move) left_up_left ()
  )
  val last = Z.Init.move
)
