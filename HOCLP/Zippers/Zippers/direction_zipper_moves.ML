(*  Title:      HOCLP/direction_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
functor Direction_Zipper_Moves(
    structure A : LAZY_IARROW
    structure M : MOVE_BASE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
  ) : HOM_ZIPPER_MOVES where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  = Hom_Zipper_Moves(
  structure M = M
  type ('i, 'a) init_from = unit
  type ('i, 'a) data = Zipper_Direction.direction
  fun init _ = A.K Zipper_Direction.Init ()
  fun up _ = A.K Zipper_Direction.Up ()
  fun down _ = A.K Zipper_Direction.Down ()
  fun left _ = A.K Zipper_Direction.Left ()
  fun right _ = A.K Zipper_Direction.Right ()
)
