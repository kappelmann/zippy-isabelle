(*  Title:      HOCLP/direction_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
functor Direction_Zipper_Moves(M : MOVE_BASE) : HOM_ZIPPER_MOVES = Hom_Zipper_Moves(
  structure M = M
  structure A = IArrow(IKleisli_IArrow_Apply(M.K.M))
  type ('i, 'a) init_from = unit
  type ('i, 'a) data = Zipper_Direction.direction
  fun init x = A.K Zipper_Direction.Init x
  fun up x = A.K Zipper_Direction.Up x
  fun down x = A.K Zipper_Direction.Down x
  fun left x = A.K Zipper_Direction.Left x
  fun right x = A.K Zipper_Direction.Right x
)
