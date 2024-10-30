(*  Title:      HOCLP/enumerable.ML
    Author:     Kevin Kappelmann
*)
signature ENUMERABLE =
sig
  include MOVE_BASE
  type ('i, 'a) init_data
  type ('i, 'a) data

  structure First : MOVE
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.cat = cat

  structure Next : HOM_MOVE
  sharing type Next.from = data
  sharing type Next.cat = cat

  structure Prev : HOM_MOVE
  sharing type Prev.from = data
  sharing type Prev.cat = cat
end

functor QEnumerable_Enumerable(
    type ('i, 'a, 'b, 'c, 'd) content
    structure E : ENUMERABLE
  ) : QENUMERABLE =
struct
structure M : MOVE_BASE = E
open M

structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content end
structure First = QMove_Move(open Base; structure M = E.First)
structure Next = Hom_QMove_Hom_Move(open Base; structure M = E.Next)
structure Prev = Hom_QMove_Hom_Move(open Base; structure M = E.Prev)

type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) First.from
type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) First.to

end

functor Enumerable_QEnumerable(E : QENUMERABLE) : ENUMERABLE =
struct
structure M : MOVE_BASE = E
open M
structure First = Move_QMove(E.First)
structure Next = Hom_Move_Hom_QMove(E.Next)
structure Prev = Hom_Move_Hom_QMove(E.Prev)
type ('i, 'a) init_data = ('i, 'a) First.from
type ('i, 'a) data = ('i, 'a) First.to
end

functor Enumerable(
    structure M : MOVE_BASE
    type ('i, 'a) init_data
    type ('i, 'a) data
    val first : ('i, ('i, 'a) init_data, ('i, 'a) data) M.move
    val next : ('i, ('i, 'a) data) M.hom_move
    val prev : ('i, ('i, 'a) data) M.hom_move
  ) : ENUMERABLE =
Enumerable_QEnumerable(QEnumerable(
  structure M = M
  type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a) init_data
  type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a) data
  val first = first
  val next = next
  val prev = prev
))

signature LAST_ENUMERABLE =
sig
  include ENUMERABLE

  structure Last : MOVE
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.cat = cat
end

functor Last_QEnumerable_Last_Enumerable(
    type ('i, 'a, 'b, 'c, 'd) content
    structure E : LAST_ENUMERABLE
  ) : LAST_QENUMERABLE =
struct
structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content end
structure BE = QEnumerable_Enumerable(open Base; structure E = E)
open BE
structure Last = QMove_Move(open Base; structure M = E.Last)
end

functor Last_Enumerable_Last_QEnumerable(BE : LAST_QENUMERABLE) : LAST_ENUMERABLE =
struct
structure E = Enumerable_QEnumerable(BE)
open E
structure Last = Move_QMove(BE.Last)
end

functor Last_Enumerable(
    structure E : ENUMERABLE
    val last : ('i, ('i, 'a) E.init_data, ('i, 'a) E.data) E.move
  ) : LAST_ENUMERABLE =
Last_Enumerable_Last_QEnumerable(Last_QEnumerable(
  structure E = QEnumerable_Enumerable(type ('i, 'a, 'b, 'c, 'd) content = 'a; structure E = E)
  val last = last
))