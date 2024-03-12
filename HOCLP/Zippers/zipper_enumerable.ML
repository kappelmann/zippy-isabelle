(*  Title:      HOCLP/zipper_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature BI_ZIPPER_ENUMERABLE =
sig
  include ZIPPER_MOVE_BASE
  type ('a, 'b) data

  structure Init : BI_ZIPPER_MOVE
  where type ('a, 'b) from = unit
  where type ('a, 'b) to = ('a, 'b) data
  sharing type Init.K.M.t = K.M.t

  structure Next : HOM_BI_ZIPPER_MOVE
  sharing type Next.from = data
  sharing type Next.K.M.t = K.M.t

  structure Prev : HOM_BI_ZIPPER_MOVE
  sharing type Prev.from = data
  sharing type Prev.K.M.t = K.M.t
end

functor Bi_Zipper_Enumerable(
    structure ZM : ZIPPER_MOVE_BASE
    type ('a, 'b) data
    val init : (unit, ('a, 'b) data) ZM.move
    val next : (('a, 'b) data, ('a, 'b) data) ZM.move
    val prev: (('a, 'b) data, ('a, 'b) data) ZM.move
  ) : BI_ZIPPER_ENUMERABLE =
struct

open ZM
type ('a, 'b) data = ('a, 'b) data

structure Init =
struct
  open ZM
  type ('a, 'b) from = unit
  type ('a, 'b) to = ('a, 'b) data
  val move = init
end

structure Next =
  Hom_Bi_Zipper_Move(structure ZM = ZM; type ('a, 'b) data = ('a, 'b) data; val move = next)
structure Prev =
  Hom_Bi_Zipper_Move(structure ZM = ZM; type ('a, 'b) data = ('a, 'b) data; val move = prev)

end

signature ZIPPER_ENUMERABLE =
sig
  include ZIPPER_MOVE_BASE
  type 'a data

  structure Init : ZIPPER_MOVE
  where type 'a from = unit
  where type 'a to = 'a data
  sharing type Init.K.M.t = K.M.t

  structure Next : HOM_ZIPPER_MOVE
  sharing type Next.from = data
  sharing type Next.K.M.t = K.M.t

  structure Prev : HOM_ZIPPER_MOVE
  sharing type Prev.from = data
  sharing type Prev.K.M.t = K.M.t
end

functor Bi_Zipper_Enumerable_Zipper_Enumerable(
    type ('a, 'b) content
    structure ZE : ZIPPER_ENUMERABLE
  ) : BI_ZIPPER_ENUMERABLE =
struct
structure ZM = Zipper_Move_Base(ZE.K)
open ZM
type ('a, 'b) data = ('a, 'b) content ZE.data
structure Init =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.Init)
structure Next =
  Hom_Bi_Zipper_Move_Hom_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.Next)
structure Prev =
  Hom_Bi_Zipper_Move_Hom_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZE.Prev)
end

functor Zipper_Enumerable_Bi_Zipper_Enumerable(ZE : BI_ZIPPER_ENUMERABLE) : ZIPPER_ENUMERABLE =
struct
structure ZM = Zipper_Move_Base(ZE.K)
open ZM
type 'a data = ('a, unit) ZE.data
structure Init = Zipper_Move_Bi_Zipper_Move(ZE.Init)
structure Next = Hom_Zipper_Move_Hom_Bi_Zipper_Move(ZE.Next)
structure Prev = Hom_Zipper_Move_Hom_Bi_Zipper_Move(ZE.Prev)
end

functor Zipper_Enumerable(
    structure ZM : ZIPPER_MOVE_BASE
    type 'a data
    val init : (unit, 'a data) ZM.move
    val next : ('a data, 'a data) ZM.move
    val prev: ('a data, 'a data) ZM.move
  ) : ZIPPER_ENUMERABLE =
Zipper_Enumerable_Bi_Zipper_Enumerable(Bi_Zipper_Enumerable(
  structure ZM = ZM
  type ('a, 'b) data = 'a data
  val init = init
  val next = next
  val prev = prev
))

functor Int_Zipper_Enumerable(ZM : ZIPPER_MOVE_BASE) : ZIPPER_ENUMERABLE = Zipper_Enumerable(
  structure ZM = ZM
  type 'a data = int
  structure A = Arrow(Kleisli_Arrow_Apply(ZM.K.M))
  val init = A.K 0
  val next = A.arr (fn p => p + 1)
  val prev = A.arr (fn p => p - 1)
)

signature ZIPPER_PATH =
sig
  type 'a path
  include HOM_ZIPPER_MOVES
  sharing type data = path
end

(*TODO: generalise other monads*)
functor Zipper_Path(ZEnum : ZIPPER_ENUMERABLE where type 'a K.M.t = 'a option) : ZIPPER_PATH =
struct

type 'a path = 'a ZEnum.data List.t

structure ZM = Hom_Zipper_Moves(
  structure ZM = ZEnum
  type 'a init_from = unit
  type 'a data = 'a path

  structure AA = Kleisli_Arrow_Apply(ZM.K.M)
  structure A = Arrow(AA)

  fun init x = x |>
    (ZEnum.Init.move
    |> A.comp (A.arr (fn pos => List.cons pos List.empty)))

  fun horizontal_move pos_move = List.dest
    |> A.comp (A.first pos_move)
    |> A.comp (A.arr (uncurry List.cons))

  fun right p = horizontal_move ZEnum.Next.move p
  fun left p = horizontal_move ZEnum.Prev.move p

  fun down p = p |>
    (A.&&& (A.K (ZEnum.Init.move, ())) (A.id ())
    |> A.comp (A.first AA.app)
    |> A.comp (A.arr (uncurry List.cons)))

  fun up p = p |> (List.dest |> A.comp (A.arr snd))
)
open ZM

end