(*  Title:      HOCLP/move.ML
    Author:     Kevin Kappelmann
*)
signature MOVE =
sig
  include MOVE_BASE
  type ('i, 'a) from
  type ('i, 'a) to
  val move : ('i, ('i, 'a) from, ('i, 'a) to) move
end

functor QMove_Move(type ('i, 'a, 'b, 'c, 'd) content; structure M : MOVE) : QMOVE =
struct
open M
type ('i, 'a, 'b, 'c, 'd) from = ('i, ('i, 'a, 'b, 'c, 'd) content) M.from
type ('i, 'a, 'b, 'c, 'd) to = ('i, ('i, 'a, 'b, 'c, 'd) content) M.to
end

functor Move_QMove(M : QMOVE) : MOVE =
struct
open M
type ('i, 'a) from = ('i, 'a, unit, unit, unit) M.from
type ('i, 'a) to = ('i, 'a, unit, unit, unit) M.to
end

signature HOM_MOVE = sig include MOVE sharing type from = to end

functor Hom_QMove_Hom_Move(type ('i, 'a, 'b, 'c, 'd) content; structure M : HOM_MOVE) : HOM_QMOVE =
QMove_Move(type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content; structure M = M)

functor Hom_Move_Hom_QMove(M : HOM_QMOVE) : HOM_MOVE = Move_QMove(M)

functor Hom_Move(
    structure M : MOVE_BASE
    type ('i, 'a) data
    val move : ('i, ('i, 'a) data) M.hom_move
  ) : HOM_MOVE =
Hom_Move_Hom_QMove(Hom_QMove(
  structure M = M
  type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a) data
  val move = move
))