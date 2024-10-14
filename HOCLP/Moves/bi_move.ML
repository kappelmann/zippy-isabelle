(*  Title:      HOCLP/bi_move.ML
    Author:     Kevin Kappelmann
*)
signature BI_MOVE =
sig
  include MOVE_BASE
  type ('i, 'a, 'b) from
  type ('i, 'a, 'b) to
  val move : ('i, ('i, 'a, 'b) from, ('i, 'a, 'b) to) move
end

signature HOM_BI_MOVE =
sig
  include BI_MOVE
  sharing type from = to
end

functor Hom_Bi_Move(
    structure M : MOVE_BASE
    type ('i, 'a, 'b) data
    val move : ('i, ('i, 'a, 'b) data) M.hom_move
  ) : HOM_BI_MOVE =
struct
open M
type ('i, 'a, 'b) from = ('i, 'a, 'b) data
type ('i, 'a, 'b) to = ('i, 'a, 'b) data
val move = move
end

functor Instantiate_Bi_Move(
    type ('i, 'a, 'b) inst1
    type ('i, 'a, 'b) inst2;
    structure M : BI_MOVE
  ) :
    BI_MOVE
    where type ('i, 'a, 'b) from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.from
    where type ('i, 'a, 'b) to = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.to
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  = M
