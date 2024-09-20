(*  Title:      HOCLP/direction_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
functor Direction_Zipper_Moves(
    structure A : IARROW
    structure M : MOVE_BASE
    sharing type M.T.cat = A.cat
  ) : HOM_ZIPPER_MOVES = Hom_Zipper_Moves(
  structure M = M
  type ('i, 'a) init_from = unit
  type ('i, 'a) data = Zipper_Direction.direction
  fun init x = A.K Zipper_Direction.Init
  fun up x = A.K Zipper_Direction.Up
  fun down x = A.K Zipper_Direction.Down
  fun left x = A.K Zipper_Direction.Left
  fun right x = A.K Zipper_Direction.Right
)
