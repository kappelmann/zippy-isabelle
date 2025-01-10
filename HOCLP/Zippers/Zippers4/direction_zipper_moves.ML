(*  Title:      HOCLP/direction_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
functor Direction_Zipper4_Moves(M : MOVE_BASE)
  : ZIPPER4_MOVES where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  = Zipper4_Moves(
  structure M = M
  structure A = Kleisli_Arrow(M.M)
  type ('i, 'a1, 'a2, 'a3, 'a4) container = Zipper_Direction.direction
  type ('i, 'a1, 'a2, 'a3, 'a4) zipper = Zipper_Direction.direction
  fun zip x = x |> A.K Zipper_Direction.Zip
  fun unzip x = x |> A.K Zipper_Direction.Unzip
  fun up x = x |> A.K Zipper_Direction.Up
  fun down x = x |> A.K Zipper_Direction.Down
  fun left x = x |> A.K Zipper_Direction.Left
  fun right x = x |> A.K Zipper_Direction.Right
)
