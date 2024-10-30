(*  Title:      HOCLP/qenumerable.ML
    Author:     Kevin Kappelmann
*)
signature QENUMERABLE =
sig
  include MOVE_BASE
  type ('i, 'a, 'b, 'c, 'd) init_data
  type ('i, 'a, 'b, 'c, 'd) data

  structure First : QMOVE
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.cat = cat

  structure Next : HOM_QMOVE
  sharing type Next.from = data
  sharing type Next.cat = cat

  structure Prev : HOM_QMOVE
  sharing type Prev.from = data
  sharing type Prev.cat = cat
end

functor QEnumerable(
    structure M : MOVE_BASE
    type ('i, 'a, 'b, 'c, 'd) init_data
    type ('i, 'a, 'b, 'c, 'd) data
    val first : ('i, ('i, 'a, 'b, 'c, 'd) init_data, ('i, 'a, 'b, 'c, 'd) data) M.move
    val next : ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
    val prev: ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
  ) : QENUMERABLE =
struct

open M
type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) init_data
type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) data

structure First =
struct
  open M
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) init_data
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) data
  val move = first
end

structure Base = struct structure M = M; type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) data end
structure Next = Hom_QMove(open Base; val move = next)
structure Prev = Hom_QMove(open Base; val move = prev)

end

signature LAST_QENUMERABLE =
sig
  include QENUMERABLE

  structure Last : QMOVE
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.cat = cat
end

functor Last_QEnumerable(
    structure E : QENUMERABLE
    val last : ('i, ('i, 'a, 'b, 'c, 'd) E.init_data, ('i, 'a, 'b, 'c, 'd) E.data) E.move
  ) : LAST_QENUMERABLE =
struct
open E

structure Last =
struct
  open E
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) init_data
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) data
  val move = last
end
end
