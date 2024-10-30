(*  Title:      HOCLP/qmove.ML
    Author:     Kevin Kappelmann
*)
signature QMOVE =
sig
  include MOVE_BASE
  type ('i, 'a, 'b, 'c, 'd) from
  type ('i, 'a, 'b, 'c, 'd) to
  val move : ('i, ('i, 'a, 'b, 'c, 'd) from, ('i, 'a, 'b, 'c, 'd) to) move
end

signature HOM_QMOVE =
sig
  include QMOVE
  sharing type from = to
end

functor Hom_QMove(
    structure M : MOVE_BASE
    type ('i, 'a, 'b, 'c, 'd) data
    val move : ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
  ) : HOM_QMOVE =
struct
open M
type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) data
type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) data
val move = move
end

functor Instantiate_QMove(
    type ('i, 'a, 'b, 'c, 'd) inst1
    type ('i, 'a, 'b, 'c, 'd) inst2
    type ('i, 'a, 'b, 'c, 'd) inst3
    type ('i, 'a, 'b, 'c, 'd) inst4
    structure M : QMOVE
  ) :
    QMOVE
    where type ('i, 'a, 'b, 'c, 'd) from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.from
    where type ('i, 'a, 'b, 'c, 'd) to = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.to
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  = M
