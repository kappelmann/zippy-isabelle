(*  Title:      HOCLP/pair_alternating_bi_zippers.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ALTERNATING_BI_ZIPPERS =
sig
  structure Z1 : BI_ZIPPER
  structure Z2 : BI_ZIPPER

  structure Down1 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper
  sharing type Down1.K.M.t = Z2.Init.K.M.t

  structure Down2 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
  sharing type Down2.K.M.t = Z1.Init.K.M.t

  structure Up1 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper

  structure Up2 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
end

functor Pair_Alternating_Bi_Zippers(
    structure AZ1 : ALTERNATING_BI_ZIPPERS
    structure AZ2 : ALTERNATING_BI_ZIPPERS
    sharing type AZ1.Z1.K.M.t = AZ2.Z1.K.M.t
    sharing type AZ1.Z2.K.M.t = AZ2.Z2.K.M.t
    sharing type AZ1.Up1.K.M.t = AZ2.Up1.K.M.t
    sharing type AZ1.Up2.K.M.t = AZ2.Up2.K.M.t
  ) :
    ALTERNATING_BI_ZIPPERS
    where type ('i, 'a, 'b) Z1.content = ('i, 'a, 'b) AZ1.Z1.content * ('i, 'a, 'b) AZ2.Z1.content
    where type ('i, 'a, 'b) Z1.zcontext = ('i, 'a, 'b) AZ1.Z1.zcontext * ('i, 'a, 'b) AZ2.Z1.zcontext
    where type ('i, 'a, 'b) Z1.zipper = ('i, 'a, 'b) AZ1.Z1.zipper * ('i, 'a, 'b) AZ2.Z1.zipper
    where type ('i, 'a, 'b) Z1.container = ('i, 'a, 'b) AZ1.Z1.container * ('i, 'a, 'b) AZ2.Z1.container
    where type ('i, 'j, 'a) Z1.K.M.t = ('i, 'j, 'a) AZ1.Z1.K.M.t
    where type ('i, 'a, 'b) Z2.content = ('i, 'a, 'b) AZ1.Z2.content * ('i, 'a, 'b) AZ2.Z2.content
    where type ('i, 'a, 'b) Z2.zcontext = ('i, 'a, 'b) AZ1.Z2.zcontext * ('i, 'a, 'b) AZ2.Z2.zcontext
    where type ('i, 'a, 'b) Z2.zipper = ('i, 'a, 'b) AZ1.Z2.zipper * ('i, 'a, 'b) AZ2.Z2.zipper
    where type ('i, 'a, 'b) Z2.container = ('i, 'a, 'b) AZ1.Z2.container * ('i, 'a, 'b) AZ2.Z2.container
    where type ('i, 'j, 'a) Z2.K.M.t = ('i, 'j, 'a)  AZ1.Z2.K.M.t
    where type ('i, 'j, 'a) Up1.K.M.t = ('i, 'j, 'a) AZ1.Up1.K.M.t
    where type ('i, 'j, 'a) Up2.K.M.t = ('i, 'j, 'a) AZ1.Up2.K.M.t
  =
struct

structure Z1 = Pair_Bi_Zipper(
  structure Z1 = AZ1.Z1
  structure Z2 = AZ2.Z1
)
structure Z2 = Pair_Bi_Zipper(
  structure Z1 = AZ1.Z2
  structure Z2 = AZ2.Z2
)

structure Down1 = Pair_Bi_Move(
  structure M1 = AZ1.Down1
  structure M2 = AZ2.Down1
)

structure Down2 = Pair_Bi_Move(
  structure M1 = AZ1.Down2
  structure M2 = AZ2.Down2
)

structure Up1 = Pair_Bi_Move(
  structure M1 = AZ1.Up1
  structure M2 = AZ2.Up1
)

structure Up2 = Pair_Bi_Move(
  structure M1 = AZ1.Up2
  structure M2 = AZ2.Up2
)

end
