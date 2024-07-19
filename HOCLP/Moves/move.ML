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

functor Bi_Move_Move(type ('i, 'a, 'b) content; structure M : MOVE) : BI_MOVE =
struct
open M
type ('i, 'a, 'b) from = ('i, ('i, 'a, 'b) content) M.from
type ('i, 'a, 'b) to = ('i, ('i, 'a, 'b) content) M.to
end

functor Move_Bi_Move(M : BI_MOVE) : MOVE =
struct
open M
type ('i, 'a) from = ('i, 'a, unit) M.from
type ('i, 'a) to = ('i, 'a, unit) M.to
end

signature HOM_MOVE = sig include MOVE sharing type from = to end

functor Hom_Bi_Move_Hom_Move(type ('i, 'a, 'b) content; structure M : HOM_MOVE) : HOM_BI_MOVE =
Bi_Move_Move(type ('i, 'a, 'b) content = ('i, 'a, 'b) content; structure M = M)

functor Hom_Move_Hom_Bi_Move(M : HOM_BI_MOVE) : HOM_MOVE = Move_Bi_Move(M)

functor Hom_Move(
    structure M : MOVE_BASE
    type ('i, 'a) data
    val move : ('i, ('i, 'a) data) M.hom_move
  ) : HOM_MOVE =
Hom_Move_Hom_Bi_Move(Hom_Bi_Move(
  structure M = M
  type ('i, 'a, 'b) data = ('i, 'a) data
  val move = move
))