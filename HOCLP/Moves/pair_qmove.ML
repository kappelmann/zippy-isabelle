(*  Title:      HOCLP/pair_qmove.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_QMOVE =
sig
  structure M1 : QMOVE
  structure M2 : QMOVE
  sharing type M1.cat = M2.cat

  include QMOVE
  where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) M1.from * ('i, 'a, 'b, 'c, 'd) M2.from
  where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) M1.to * ('i, 'a, 'b, 'c, 'd) M2.to
  sharing type M1.cat = cat
  sharing type M2.cat = cat
end

functor Pair_QMove(
    structure A : LAZY_IARROW_BASE
    structure M1 : QMOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.cat
    structure M2 : QMOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M1.cat
  ) : PAIR_QMOVE
  =
struct

structure M1 = M1
structure M2 = M2

structure M : MOVE_BASE = M1
open M

type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) M1.from * ('i, 'a, 'b, 'c, 'd) M2.from
type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) M1.to * ('i, 'a, 'b, 'c, 'd) M2.to

fun move _ = A.*** (M1.move, M2.move) ()

end
