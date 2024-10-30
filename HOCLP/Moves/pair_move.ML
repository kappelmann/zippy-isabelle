(*  Title:      HOCLP/pair_move.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_MOVE =
sig
  structure M1 : MOVE
  structure M2 : MOVE
  sharing type M1.cat = M2.cat

  include MOVE
  where type ('i, 'a) from = ('i, 'a) M1.from * ('i, 'a) M2.from
  where type ('i, 'a) to = ('i, 'a) M1.to * ('i, 'a) M2.to
  sharing type M1.cat = cat
  sharing type M2.cat = cat
end

functor Pair_QMove_Pair_Move(type ('i, 'a, 'b, 'c, 'd) content; structure PM : PAIR_MOVE) : PAIR_QMOVE =
struct
structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content end
structure M1 = QMove_Move(open Base; structure M = PM.M1)
structure M2 = QMove_Move(open Base; structure M = PM.M2)
structure M = QMove_Move(open Base; structure M = PM)
open M
end

functor Pair_Move_Pair_QMove(PM : PAIR_QMOVE) : PAIR_MOVE =
struct
structure M1 = Move_QMove(PM.M1)
structure M2 = Move_QMove(PM.M2)
structure M = Move_QMove(PM)
open M
end

functor Pair_Move(
    structure A : LAZY_IARROW_BASE
    structure M1 : MOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
    structure M2 : MOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M1.cat
  ) : PAIR_MOVE =
Pair_Move_Pair_QMove(Pair_QMove(
  structure A = A
  structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = 'a end
  structure M1 = QMove_Move(open Base; structure M = M1)
  structure M2 = QMove_Move(open Base; structure M = M2)
))
