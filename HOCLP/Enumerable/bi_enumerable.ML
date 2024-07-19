(*  Title:      HOCLP/bi_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature BI_ENUMERABLE =
sig
  include MOVE_BASE
  type ('i, 'a, 'b) init_data
  type ('i, 'a, 'b) data

  structure First : BI_MOVE
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.K.M.t = K.M.t

  structure Next : HOM_BI_MOVE
  sharing type Next.from = data
  sharing type Next.K.M.t = K.M.t

  structure Prev : HOM_BI_MOVE
  sharing type Prev.from = data
  sharing type Prev.K.M.t = K.M.t
end

functor Bi_Enumerable(
    structure M : MOVE_BASE
    type ('i, 'a, 'b) init_data
    type ('i, 'a, 'b) data
    val first : ('i, ('i, 'a, 'b) init_data, ('i, 'a, 'b) data) M.move
    val next : ('i, ('i, 'a, 'b) data) M.hom_move
    val prev: ('i, ('i, 'a, 'b) data) M.hom_move
  ) : BI_ENUMERABLE =
struct

open M
type ('i, 'a, 'b) init_data = ('i, 'a, 'b) init_data
type ('i, 'a, 'b) data = ('i, 'a, 'b) data

structure First =
struct
  open M
  type ('i, 'a, 'b) from = ('i, 'a, 'b) init_data
  type ('i, 'a, 'b) to = ('i, 'a, 'b) data
  val move = first
end

structure Base = struct structure M = M; type ('i, 'a, 'b) data = ('i, 'a, 'b) data end
structure Next = Hom_Bi_Move(open Base; val move = next)
structure Prev = Hom_Bi_Move(open Base; val move = prev)

end

signature LAST_BI_ENUMERABLE =
sig
  include BI_ENUMERABLE

  structure Last : BI_MOVE
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.K.M.t = K.M.t
end

functor Last_Bi_Enumerable(
    structure E : BI_ENUMERABLE
    val last : ('i, ('i, 'a, 'b) E.init_data, ('i, 'a, 'b) E.data) E.move
  ) : LAST_BI_ENUMERABLE =
struct
open E

structure Last =
struct
  open E
  type ('i, 'a, 'b) from = ('i, 'a, 'b) init_data
  type ('i, 'a, 'b) to = ('i, 'a, 'b) data
  val move = last
end
end
