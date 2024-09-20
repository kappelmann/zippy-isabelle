(*  Title:      HOCLP/pair_alternating_bi_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Pair_Alternating_Bi_Zippers(
    structure A1 : LAZY_IARROW_BASE
    structure A2 : LAZY_IARROW_BASE
    structure AU1 : LAZY_IARROW_BASE
    structure AU2 : LAZY_IARROW_BASE
    structure AZ1 : ALTERNATING_BI_ZIPPERS
    sharing type AZ1.Z1.T.cat = A1.T.cat
    sharing type AZ1.Z2.T.cat = A2.T.cat
    sharing type AZ1.Up1.T.cat = AU1.T.cat
    sharing type AZ1.Up2.T.cat = AU2.T.cat
    structure AZ2 : ALTERNATING_BI_ZIPPERS
    sharing type AZ1.Z1.T.cat = AZ2.Z1.T.cat
    sharing type AZ1.Z2.T.cat = AZ2.Z2.T.cat
    sharing type AZ1.Up1.T.cat = AZ2.Up1.T.cat
    sharing type AZ1.Up2.T.cat = AZ2.Up2.T.cat
  ) :
    ALTERNATING_BI_ZIPPERS
    where type ('i, 'a, 'b) Z1.content = ('i, 'a, 'b) AZ1.Z1.content * ('i, 'a, 'b) AZ2.Z1.content
    where type ('i, 'a, 'b) Z1.zcontext = ('i, 'a, 'b) AZ1.Z1.zcontext * ('i, 'a, 'b) AZ2.Z1.zcontext
    where type ('i, 'a, 'b) Z1.zipper = ('i, 'a, 'b) AZ1.Z1.zipper * ('i, 'a, 'b) AZ2.Z1.zipper
    where type ('i, 'a, 'b) Z1.container = ('i, 'a, 'b) AZ1.Z1.container * ('i, 'a, 'b) AZ2.Z1.container
    where type ('i, 'j, 'a, 'b) Z1.T.cat = ('i, 'j, 'a, 'b) AZ1.Z1.T.cat
    where type ('i, 'a, 'b) Z2.content = ('i, 'a, 'b) AZ1.Z2.content * ('i, 'a, 'b) AZ2.Z2.content
    where type ('i, 'a, 'b) Z2.zcontext = ('i, 'a, 'b) AZ1.Z2.zcontext * ('i, 'a, 'b) AZ2.Z2.zcontext
    where type ('i, 'a, 'b) Z2.zipper = ('i, 'a, 'b) AZ1.Z2.zipper * ('i, 'a, 'b) AZ2.Z2.zipper
    where type ('i, 'a, 'b) Z2.container = ('i, 'a, 'b) AZ1.Z2.container * ('i, 'a, 'b) AZ2.Z2.container
    where type ('i, 'j, 'a, 'b) Z2.T.cat = ('i, 'j, 'a, 'b)  AZ1.Z2.T.cat
    where type ('i, 'j, 'a, 'b) Up1.T.cat = ('i, 'j, 'a, 'b) AZ1.Up1.T.cat
    where type ('i, 'j, 'a, 'b) Up2.T.cat = ('i, 'j, 'a, 'b) AZ1.Up2.T.cat
  =
struct

structure Z1 = Pair_Bi_Zipper(
  structure A = A1
  structure Z1 = AZ1.Z1
  structure Z2 = AZ2.Z1
)
structure Z2 = Pair_Bi_Zipper(
  structure A = A2
  structure Z1 = AZ1.Z2
  structure Z2 = AZ2.Z2
)

structure Down1 = Pair_Bi_Move(
  structure A = A2
  structure M1 = AZ1.Down1
  structure M2 = AZ2.Down1
)

structure Down2 = Pair_Bi_Move(
  structure A = A1
  structure M1 = AZ1.Down2
  structure M2 = AZ2.Down2
)

structure Up1 = Pair_Bi_Move(
  structure A = AU1
  structure M1 = AZ1.Up1
  structure M2 = AZ2.Up1
)

structure Up2 = Pair_Bi_Move(
  structure A = AU2
  structure M1 = AZ1.Up2
  structure M2 = AZ2.Up2
)

end
