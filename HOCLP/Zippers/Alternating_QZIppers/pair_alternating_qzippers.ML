(*  Title:      HOCLP/pair_alternating_qzippers.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ALTERNATING_QZIPPERS =
sig
  structure AZ1 : ALTERNATING_QZIPPERS
  structure AZ2 : ALTERNATING_QZIPPERS
  where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AZ1.Z1.cat
  where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) AZ1.Z2.cat
  where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) AZ1.Z3.cat
  where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) AZ1.Z4.cat
  where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) AZ1.Down1.cat
  where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) AZ1.Down2.cat
  where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) AZ1.Down3.cat
  where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) AZ1.Down4.cat
  where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AZ1.Up1.cat
  where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AZ1.Up2.cat
  where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) AZ1.Up3.cat
  where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) AZ1.Up4.cat

  include ALTERNATING_QZIPPERS
  where type ('i, 'a, 'b, 'c, 'd) Z1.content =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z1.content * ('i, 'a, 'b, 'c, 'd) AZ2.Z1.content
  where type ('i, 'a, 'b, 'c, 'd) Z1.zcontext =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z1.zcontext * ('i, 'a, 'b, 'c, 'd) AZ2.Z1.zcontext
  where type ('i, 'a, 'b, 'c, 'd) Z1.zipper =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z1.zipper * ('i, 'a, 'b, 'c, 'd) AZ2.Z1.zipper
  where type ('i, 'a, 'b, 'c, 'd) Z1.container =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z1.container * ('i, 'a, 'b, 'c, 'd) AZ2.Z1.container
  where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AZ1.Z1.cat
  where type ('i, 'a, 'b, 'c, 'd) Z2.content =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z2.content * ('i, 'a, 'b, 'c, 'd) AZ2.Z2.content
  where type ('i, 'a, 'b, 'c, 'd) Z2.zcontext =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z2.zcontext * ('i, 'a, 'b, 'c, 'd) AZ2.Z2.zcontext
  where type ('i, 'a, 'b, 'c, 'd) Z2.zipper =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z2.zipper * ('i, 'a, 'b, 'c, 'd) AZ2.Z2.zipper
  where type ('i, 'a, 'b, 'c, 'd) Z2.container =
    ('i, 'a, 'b, 'c, 'd) AZ1.Z2.container * ('i, 'a, 'b, 'c, 'd) AZ2.Z2.container
  where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b)  AZ1.Z2.cat
  where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AZ1.Up1.cat
  where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AZ1.Up2.cat
end

functor Pair_Alternating_QZippers(
    structure A1 : LAZY_IARROW_BASE
    structure A2 : LAZY_IARROW_BASE
    structure A3 : LAZY_IARROW_BASE
    structure A4 : LAZY_IARROW_BASE
    structure AD1 : LAZY_IARROW_BASE
    structure AD2 : LAZY_IARROW_BASE
    structure AD3 : LAZY_IARROW_BASE
    structure AD4 : LAZY_IARROW_BASE
    structure AU1 : LAZY_IARROW_BASE
    structure AU2 : LAZY_IARROW_BASE
    structure AU3 : LAZY_IARROW_BASE
    structure AU4 : LAZY_IARROW_BASE
    structure AZ1 : ALTERNATING_QZIPPERS
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) A1.cat
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) A2.cat
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) A3.cat
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) A4.cat
    where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) AD1.cat
    where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) AD2.cat
    where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) AD3.cat
    where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) AD4.cat
    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AU1.cat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AU2.cat
    where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) AU3.cat
    where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) AU4.cat
    structure AZ2 : ALTERNATING_QZIPPERS
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AZ1.Z1.cat
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) AZ1.Z2.cat
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) AZ1.Z3.cat
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) AZ1.Z4.cat
    where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) AZ1.Down1.cat
    where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) AZ1.Down2.cat
    where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) AZ1.Down3.cat
    where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) AZ1.Down4.cat
    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AZ1.Up1.cat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AZ1.Up2.cat
    where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) AZ1.Up3.cat
    where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) AZ1.Up4.cat
  ) : PAIR_ALTERNATING_QZIPPERS
  =
struct

structure AZ1 = AZ1
structure AZ2 = AZ2

structure Z1 = Pair_QZipper(
  structure A = A1
  structure Z1 = AZ1.Z1
  structure Z2 = AZ2.Z1
)
structure Z2 = Pair_QZipper(
  structure A = A2
  structure Z1 = AZ1.Z2
  structure Z2 = AZ2.Z2
)
structure Z3 = Pair_QZipper(
  structure A = A3
  structure Z1 = AZ1.Z3
  structure Z2 = AZ2.Z3
)
structure Z4 = Pair_QZipper(
  structure A = A4
  structure Z1 = AZ1.Z4
  structure Z2 = AZ2.Z4
)

structure Down1 = Pair_QMove(
  structure A = AD1
  structure M1 = AZ1.Down1
  structure M2 = AZ2.Down1
)
structure Down2 = Pair_QMove(
  structure A = AD2
  structure M1 = AZ1.Down2
  structure M2 = AZ2.Down2
)
structure Down3 = Pair_QMove(
  structure A = AD3
  structure M1 = AZ1.Down3
  structure M2 = AZ2.Down3
)
structure Down4 = Pair_QMove(
  structure A = AD4
  structure M1 = AZ1.Down4
  structure M2 = AZ2.Down4
)

structure Up1 = Pair_QMove(
  structure A = AU1
  structure M1 = AZ1.Up1
  structure M2 = AZ2.Up1
)
structure Up2 = Pair_QMove(
  structure A = AU2
  structure M1 = AZ1.Up2
  structure M2 = AZ2.Up2
)
structure Up3 = Pair_QMove(
  structure A = AU3
  structure M1 = AZ1.Up3
  structure M2 = AZ2.Up3
)
structure Up4 = Pair_QMove(
  structure A = AU4
  structure M1 = AZ1.Up4
  structure M2 = AZ2.Up4
)

end
