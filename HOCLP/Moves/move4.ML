(*  Title:      HOCLP/move4.ML
    Author:     Kevin Kappelmann

See typeclass_base.ML in ML_Typeclasses for an explanation of the 'p1 type variables.
*)
signature MOVE4 =
sig
  include MOVE_BASE
  type ('p1, 'a1, 'a2, 'a3, 'a4) from
  type ('p1, 'a1, 'a2, 'a3, 'a4) to
  val move : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) from, ('p1, 'a1, 'a2, 'a3, 'a4) to) move
end

signature HOM_MOVE4 =
sig
  include MOVE4
  sharing type from = to
end

functor Hom_Move4(
    structure M : MOVE_BASE
    type ('p1, 'a1, 'a2, 'a3, 'a4) data
    val move : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) data) M.hom_move
  ) : HOM_MOVE4 =
struct
open M
type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) data
type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) data
val move = move
end

functor Instantiate_Move4(
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst4
    structure M : MOVE4
  ) :
    MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) M.from
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) M.to
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M.cat
  = M
