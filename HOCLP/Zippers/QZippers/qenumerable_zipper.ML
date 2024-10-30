(*  Title:      HOCLP/qenumerable_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Z.Init.move moves to leftmost, topmost node
2) Z.Down.move moves to leftmost child*)
functor DFS_Postorder_Enumerable_QZipper(
    structure AE : LAZY_IARROW_EXCEPTION_REC
    structure Z : QZIPPER
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.T.lcat
  ) :
    LAST_QENUMERABLE
    where type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) Z.Init.from
    where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) Z.data
  =
Last_QEnumerable(
  structure SC = ISemi_Category(AE) open SC
  fun left_up_left _ = AE.catch' Z.Left.move (left_up_left o Z.Up.move) ()
  structure E = QEnumerable(
    structure M = Z
    type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) Z.Init.from
    type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) Z.data
    fun repeat_down _ = AE.repeat Z.Down.move ()
    fun first _ = (repeat_down o Z.Init.move) ()
    fun next _ = AE.catch' (repeat_down o Z.Right.move) Z.Up.move ()
    fun prev _ = AE.catch' (AE.repeat Z.Right.move o Z.Down.move) left_up_left ()
  )
  val last = Z.Init.move
)
