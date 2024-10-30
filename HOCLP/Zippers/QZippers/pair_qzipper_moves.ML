(*  Title:      HOCLP/pair_qzipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_QZIPPER_MOVES =
sig
  structure M1 : QZIPPER_MOVES
  structure M2 : QZIPPER_MOVES

  include QZIPPER_MOVES
  where type ('i, 'a, 'b, 'c, 'd) Init.from =
    ('i, 'a, 'b, 'c, 'd) M1.Init.from * ('i, 'a, 'b, 'c, 'd) M2.Init.from
  where type ('i, 'a, 'b, 'c, 'd) Init.to =
    ('i, 'a, 'b, 'c, 'd) M1.Init.to * ('i, 'a, 'b, 'c, 'd) M2.Init.to
  where type ('i, 'a, 'b, 'c, 'd) Up.from =
    ('i, 'a, 'b, 'c, 'd) M1.Up.from * ('i, 'a, 'b, 'c, 'd) M2.Up.from
  where type ('i, 'a, 'b, 'c, 'd) Up.to =
    ('i, 'a, 'b, 'c, 'd) M1.Up.to * ('i, 'a, 'b, 'c, 'd) M2.Up.to
  where type ('i, 'a, 'b, 'c, 'd) Down.from =
    ('i, 'a, 'b, 'c, 'd) M1.Down.from * ('i, 'a, 'b, 'c, 'd) M2.Down.from
  where type ('i, 'a, 'b, 'c, 'd) Down.to =
    ('i, 'a, 'b, 'c, 'd) M1.Down.to * ('i, 'a, 'b, 'c, 'd) M2.Down.to
  where type ('i, 'a, 'b, 'c, 'd) Left.from =
    ('i, 'a, 'b, 'c, 'd) M1.Left.from * ('i, 'a, 'b, 'c, 'd) M2.Left.from
  where type ('i, 'a, 'b, 'c, 'd) Left.to =
    ('i, 'a, 'b, 'c, 'd) M1.Left.to * ('i, 'a, 'b, 'c, 'd) M2.Left.to
  where type ('i, 'a, 'b, 'c, 'd) Right.from =
    ('i, 'a, 'b, 'c, 'd) M1.Right.from * ('i, 'a, 'b, 'c, 'd) M2.Right.from
  where type ('i, 'a, 'b, 'c, 'd) Right.to =
    ('i, 'a, 'b, 'c, 'd) M1.Right.to * ('i, 'a, 'b, 'c, 'd) M2.Right.to
  sharing type M1.cat = cat
  sharing type M2.cat = cat
end

functor Pair_QZipper_Moves(
    structure A : LAZY_IARROW_BASE
    structure M1 : QZIPPER_MOVES
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
    structure M2 : QZIPPER_MOVES
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M1.cat
  ) : PAIR_QZIPPER_MOVES =
struct

structure M1 = M1
structure M2 = M2

structure M : MOVE_BASE = M1
open M

structure Base = struct structure A = A end
structure Init = Pair_QMove(open Base; structure M1 = M1.Init; structure M2 = M2.Init)
structure Up = Pair_QMove(open Base; structure M1 = M1.Up; structure M2 = M2.Up)
structure Down = Pair_QMove(open Base; structure M1 = M1.Down; structure M2 = M2.Down)
structure Left = Pair_QMove(open Base; structure M1 = M1.Left; structure M2 = M2.Left)
structure Right = Pair_QMove(open Base; structure M1 = M1.Right; structure M2 = M2.Right)

end
