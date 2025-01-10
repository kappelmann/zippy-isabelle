(*  Title:      HOCLP/enumerable4.ML
    Author:     Kevin Kappelmann
*)
signature ENUMERABLE4 =
sig
  include MOVE_BASE
  type ('p1, 'a1, 'a2, 'a3, 'a4) init_data
  type ('p1, 'a1, 'a2, 'a3, 'a4) data

  structure First : MOVE4
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.M.t = M.t

  structure Next : HOM_MOVE4
  sharing type Next.from = data
  sharing type Next.M.t = M.t

  structure Prev : HOM_MOVE4
  sharing type Prev.from = data
  sharing type Prev.M.t = M.t
end

functor Enumerable4(
    structure M : MOVE_BASE
    type ('p1, 'a1, 'a2, 'a3, 'a4) init_data
    type ('p1, 'a1, 'a2, 'a3, 'a4) data
    val first : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) init_data, ('p1, 'a1, 'a2, 'a3, 'a4) data) M.move
    val next : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) data) M.hom_move
    val prev: ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) data) M.hom_move
  ) : ENUMERABLE4 =
struct

structure Min = M
open M
type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) init_data
type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) data

structure First =
struct
  open Min
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) init_data
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) data
  val move = first
end

structure Base =
  struct structure M = Min; type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) data end
structure Next = Hom_Move4(open Base; val move = next)
structure Prev = Hom_Move4(open Base; val move = prev)

end

signature LAST_ENUMERABLE4 =
sig
  include ENUMERABLE4
  structure Last : MOVE4
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.M.t = M.t
end

functor Last_Enumerable4(
    structure E : ENUMERABLE4
    val last : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) E.init_data, ('p1, 'a1, 'a2, 'a3, 'a4) E.data) E.move
  ) : LAST_ENUMERABLE4 =
struct
open E

structure Last =
struct
  open E
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) init_data
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) data
  val move = last
end

end
