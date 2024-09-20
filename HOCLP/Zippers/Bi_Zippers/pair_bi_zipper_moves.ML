(*  Title:      HOCLP/pair_bi_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_BI_ZIPPER_MOVES =
sig
  structure M1 : BI_ZIPPER_MOVES
  structure M2 : BI_ZIPPER_MOVES

  include BI_ZIPPER_MOVES
  where type ('i, 'a, 'b) Init.from = ('i, 'a, 'b) M1.Init.from * ('i, 'a, 'b) M2.Init.from
  where type ('i, 'a, 'b) Init.to = ('i, 'a, 'b) M1.Init.to * ('i, 'a, 'b) M2.Init.to
  where type ('i, 'a, 'b) Up.from = ('i, 'a, 'b) M1.Up.from * ('i, 'a, 'b) M2.Up.from
  where type ('i, 'a, 'b) Up.to = ('i, 'a, 'b) M1.Up.to * ('i, 'a, 'b) M2.Up.to
  where type ('i, 'a, 'b) Down.from = ('i, 'a, 'b) M1.Down.from * ('i, 'a, 'b) M2.Down.from
  where type ('i, 'a, 'b) Down.to = ('i, 'a, 'b) M1.Down.to * ('i, 'a, 'b) M2.Down.to
  where type ('i, 'a, 'b) Left.from = ('i, 'a, 'b) M1.Left.from * ('i, 'a, 'b) M2.Left.from
  where type ('i, 'a, 'b) Left.to = ('i, 'a, 'b) M1.Left.to * ('i, 'a, 'b) M2.Left.to
  where type ('i, 'a, 'b) Right.from = ('i, 'a, 'b) M1.Right.from * ('i, 'a, 'b) M2.Right.from
  where type ('i, 'a, 'b) Right.to = ('i, 'a, 'b) M1.Right.to * ('i, 'a, 'b) M2.Right.to
  sharing type M1.T.cat = T.cat
  sharing type M2.T.cat = T.cat
end

functor Pair_Bi_Zipper_Moves(
    structure A : LAZY_IARROW_BASE
    structure M1 : BI_ZIPPER_MOVES
    sharing type M1.T.cat = A.T.cat
    structure M2 : BI_ZIPPER_MOVES
    sharing type M2.T.cat = M1.T.cat
  ) : PAIR_BI_ZIPPER_MOVES =
struct

structure M1 = M1
structure M2 = M2

structure M : MOVE_BASE = M1
open M

structure Base = struct structure A = A end
structure Init = Pair_Bi_Move(open Base; structure M1 = M1.Init; structure M2 = M2.Init)
structure Up = Pair_Bi_Move(open Base; structure M1 = M1.Up; structure M2 = M2.Up)
structure Down = Pair_Bi_Move(open Base; structure M1 = M1.Down; structure M2 = M2.Down)
structure Left = Pair_Bi_Move(open Base; structure M1 = M1.Left; structure M2 = M2.Left)
structure Right = Pair_Bi_Move(open Base; structure M1 = M1.Right; structure M2 = M2.Right)

end
