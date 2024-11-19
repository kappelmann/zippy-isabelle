(*  Title:      HOCLP/direction_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
functor Direction_Zipper4_Moves(
    structure A : LAZY_ARROW
    structure M : MOVE_BASE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.cat
  ) : ZIPPER4_MOVES where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M.cat
  = Zipper4_Moves(
  structure M = M
  type ('i, 'a1, 'a2, 'a3, 'a4) container = Zipper_Direction.direction
  type ('i, 'a1, 'a2, 'a3, 'a4) zipper = Zipper_Direction.direction
  fun zip _ = A.K Zipper_Direction.Zip
    |> Lazy_Cat_Util.unlift
  fun unzip _ = A.K Zipper_Direction.Unzip
    |> Lazy_Cat_Util.unlift
  fun up _ = A.K Zipper_Direction.Up
    |> Lazy_Cat_Util.unlift
  fun down _ = A.K Zipper_Direction.Down
    |> Lazy_Cat_Util.unlift
  fun left _ = A.K Zipper_Direction.Left
    |> Lazy_Cat_Util.unlift
  fun right _ = A.K Zipper_Direction.Right
    |> Lazy_Cat_Util.unlift
)
