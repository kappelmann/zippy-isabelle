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
  sharing type First.C.cat = C.cat

  structure Next : HOM_MOVE
  sharing type Next.from = data
  sharing type Next.C.cat = C.cat

  structure Prev : HOM_MOVE
  sharing type Prev.from = data
  sharing type Prev.C.cat = C.cat
end

functor Bi_Enumerable_Enumerable(
    type ('i, 'a, 'b) content
    structure E : ENUMERABLE
  ) : BI_ENUMERABLE =
struct
structure M = Move_Base(E.C)
open M

structure Base = struct type ('i, 'a, 'b) content = ('i, 'a, 'b) content end
structure First = Bi_Move_Move(open Base; structure M = E.First)
structure Next = Hom_Bi_Move_Hom_Move(open Base; structure M = E.Next)
structure Prev = Hom_Bi_Move_Hom_Move(open Base; structure M = E.Prev)

type ('i, 'a, 'b) init_data = ('i, 'a, 'b) First.from
type ('i, 'a, 'b) data = ('i, 'a, 'b) First.to

end

functor Enumerable_Bi_Enumerable(E : BI_ENUMERABLE) : ENUMERABLE =
struct
structure M = Move_Base(E.C)
open M
structure First = Move_Bi_Move(E.First)
structure Next = Hom_Move_Hom_Bi_Move(E.Next)
structure Prev = Hom_Move_Hom_Bi_Move(E.Prev)
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
Enumerable_Bi_Enumerable(Bi_Enumerable(
  structure M = M
  type ('i, 'a, 'b) init_data = ('i, 'a) init_data
  type ('i, 'a, 'b) data = ('i, 'a) data
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
  sharing type Last.C.cat = C.cat
end

functor Last_Bi_Enumerable_Last_Enumerable(
    type ('i, 'a, 'b) content
    structure E : LAST_ENUMERABLE
  ) : LAST_BI_ENUMERABLE =
struct
structure Base = struct type ('i, 'a, 'b) content = ('i, 'a, 'b) content end
structure BE = Bi_Enumerable_Enumerable(open Base; structure E = E)
open BE
structure Last = Bi_Move_Move(open Base; structure M = E.Last)
end

functor Last_Enumerable_Last_Bi_Enumerable(BE : LAST_BI_ENUMERABLE) : LAST_ENUMERABLE =
struct
structure E = Enumerable_Bi_Enumerable(BE)
open E
structure Last = Move_Bi_Move(BE.Last)
end

functor Last_Enumerable(
    structure E : ENUMERABLE
    val last : ('i, ('i, 'a) E.init_data, ('i, 'a) E.data) E.move
  ) : LAST_ENUMERABLE =
Last_Enumerable_Last_Bi_Enumerable(Last_Bi_Enumerable(
  structure E = Bi_Enumerable_Enumerable(type ('i, 'a, 'b) content = 'a; structure E = E)
  val last = last
))