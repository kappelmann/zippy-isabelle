(*  Title:      HOCLP/zipper_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_ENUMERABLE =
sig
  include ZIPPER_MOVE_BASE
  type 'a init_data
  type 'a data

  structure First : ZIPPER_MOVE
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.K.M.t = K.M.t

  structure Next : HOM_ZIPPER_MOVE
  sharing type Next.from = data
  sharing type Next.K.M.t = K.M.t
end

functor Bi_Zipper_Enumerable_Zipper_Enumerable(
    type ('a, 'b) content
    structure ZE : ZIPPER_ENUMERABLE
  ) : BI_ZIPPER_ENUMERABLE =
struct
structure ZM = Zipper_Move_Base(ZE.K)
open ZM
type ('a, 'b) init_data = ('a, 'b) content ZE.init_data
type ('a, 'b) data = ('a, 'b) content ZE.data
structure First =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.First)
structure Next =
  Hom_Bi_Zipper_Move_Hom_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.Next)
end

functor Zipper_Enumerable_Bi_Zipper_Enumerable(ZE : BI_ZIPPER_ENUMERABLE) : ZIPPER_ENUMERABLE =
struct
structure ZM = Zipper_Move_Base(ZE.K)
open ZM
type 'a init_data = ('a, unit) ZE.init_data
type 'a data = ('a, unit) ZE.data
structure First = Zipper_Move_Bi_Zipper_Move(ZE.First)
structure Next = Hom_Zipper_Move_Hom_Bi_Zipper_Move(ZE.Next)
end

functor Zipper_Enumerable(
    structure ZM : ZIPPER_MOVE_BASE
    type 'a init_data
    type 'a data
    val first : ('a init_data, 'a data) ZM.move
    val next : ('a data, 'a data) ZM.move
  ) : ZIPPER_ENUMERABLE =
Zipper_Enumerable_Bi_Zipper_Enumerable(Bi_Zipper_Enumerable(
  structure ZM = ZM
  type ('a, 'b) init_data = 'a init_data
  type ('a, 'b) data = 'a data
  val first = first
  val next = next
))

signature ZIPPER_BI_ENUMERABLE =
sig
  include ZIPPER_ENUMERABLE

  structure Last : ZIPPER_MOVE
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.K.M.t = K.M.t

  structure Prev : HOM_ZIPPER_MOVE
  sharing type Prev.from = data
  sharing type Prev.K.M.t = K.M.t
end

functor Bi_Zipper_Bi_Enumerable_Bi_Zipper_Enumerable(
    type ('a, 'b) content
    structure ZE : ZIPPER_BI_ENUMERABLE
  ) : BI_ZIPPER_BI_ENUMERABLE =
struct
structure BZE = Bi_Zipper_Enumerable_Zipper_Enumerable(type ('a, 'b) content = ('a, 'b) content; structure ZE = ZE)
open BZE

structure Last =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.Last)
structure Prev =
  Hom_Bi_Zipper_Move_Hom_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.Prev)
end

functor Zipper_Bi_Enumerable_Bi_Zipper_Bi_Enumerable(BZE : BI_ZIPPER_BI_ENUMERABLE) : ZIPPER_BI_ENUMERABLE =
struct
structure ZE = Zipper_Enumerable_Bi_Zipper_Enumerable(BZE)
open ZE

structure Last = Zipper_Move_Bi_Zipper_Move(BZE.Last)
structure Prev = Hom_Zipper_Move_Hom_Bi_Zipper_Move(BZE.Prev)
end

functor Zipper_Bi_Enumerable(
    structure ZE : ZIPPER_ENUMERABLE
    val last : ('a ZE.init_data, 'a ZE.data) ZE.move
    val prev : ('a ZE.data, 'a ZE.data) ZE.move
  ) : ZIPPER_BI_ENUMERABLE =
Zipper_Bi_Enumerable_Bi_Zipper_Bi_Enumerable(Bi_Zipper_Bi_Enumerable(
  structure BZE = Bi_Zipper_Enumerable_Zipper_Enumerable(type ('a, 'b) content = 'a; structure ZE = ZE)
  val last = last
  val prev = prev
))

functor Int_Zipper_Enumerable(ZM : ZIPPER_MOVE_BASE) : ZIPPER_ENUMERABLE = Zipper_Enumerable(
  structure ZM = ZM
  structure A = Arrow(Kleisli_Arrow_Apply(ZM.K.M))
  type 'a init_data = unit
  type 'a data = int
  val first = A.K 0
  val next = A.arr (fn p => p + 1)
)
