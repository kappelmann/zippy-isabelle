(*  Title:      HOCLP/pair_bi_move.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_BI_MOVE =
sig
  structure M1 : BI_MOVE
  structure M2 : BI_MOVE
  sharing type M1.cat = M2.cat

  include BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) M1.from * ('i, 'a, 'b) M2.from
  where type ('i, 'a, 'b) to = ('i, 'a, 'b) M1.to * ('i, 'a, 'b) M2.to
  sharing type M1.cat = cat
  sharing type M2.cat = cat
end

functor Pair_Bi_Move(
    structure A : LAZY_IARROW_BASE
    structure M1 : BI_MOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.cat
    structure M2 : BI_MOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M1.cat
  ) : PAIR_BI_MOVE
  =
struct

structure M1 = M1
structure M2 = M2

structure M : MOVE_BASE = M1
open M

type ('i, 'a, 'b) from = ('i, 'a, 'b) M1.from * ('i, 'a, 'b) M2.from
type ('i, 'a, 'b) to = ('i, 'a, 'b) M1.to * ('i, 'a, 'b) M2.to

fun move _ = A.*** (M1.move, M2.move) ()

end
