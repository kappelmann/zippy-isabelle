(*  Title:      HOCLP/alternating_zippers4.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_ZIPPERS4_MOVES =
sig
  include MOVE_BASE
  structure Z1 : ZIPPER4_MOVES
  sharing type Z1.cat = cat
  structure Z2 : ZIPPER4_MOVES
  sharing type Z2.cat = cat
  structure Z3 : ZIPPER4_MOVES
  sharing type Z3.cat = cat
  structure Z4 : ZIPPER4_MOVES
  sharing type Z4.cat = cat

  structure Down1 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  sharing type Down1.cat = cat

  structure Down2 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  sharing type Down2.cat = cat

  structure Down3 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  sharing type Down3.cat = cat

  structure Down4 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  sharing type Down4.cat = cat

  structure Up1 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  sharing type Up1.cat = cat

  structure Up2 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  sharing type Up2.cat = cat

  structure Up3 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  sharing type Up3.cat = cat

  structure Up4 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  sharing type Up4.cat = cat
end

signature ALTERNATING_ZIPPERS4 =
sig
  include MOVE_BASE
  structure L : LENS
  structure Z1 : ZIPPER4
  sharing type Z1.cat = cat
  sharing type Z1.ZO.L.lens = L.lens
  structure Z2 : ZIPPER4
  sharing type Z2.cat = cat
  sharing type Z2.ZO.L.lens = L.lens
  structure Z3 : ZIPPER4
  sharing type Z3.cat = cat
  sharing type Z3.ZO.L.lens = L.lens
  structure Z4 : ZIPPER4
  sharing type Z4.cat = cat
  sharing type Z4.ZO.L.lens = L.lens

  structure Down1 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  sharing type Down1.cat = cat

  structure Down2 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  sharing type Down2.cat = cat

  structure Down3 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  sharing type Down3.cat = cat

  structure Down4 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  sharing type Down4.cat = cat

  structure Up1 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  sharing type Up1.cat = cat

  structure Up2 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  sharing type Up2.cat = cat

  structure Up3 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  sharing type Up3.cat = cat

  structure Up4 : MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  sharing type Up4.cat = cat
end

functor Alternating_Zippers4(
    structure A : ALTERNATING_ZIPPERS4_MOVES
    structure ZO1 : ZIPPER4_OPTICS
    sharing type ZO1.zipper = A.Z1.zipper
    sharing type ZO1.L.C.cat = A.Z1.cat
    structure ZO2 : ZIPPER4_OPTICS
    sharing type ZO2.zipper = A.Z2.zipper
    sharing type ZO2.L.C.cat = A.Z2.cat
    sharing type ZO2.L.lens = ZO1.L.lens
    structure ZO3 : ZIPPER4_OPTICS
    sharing type ZO3.zipper = A.Z3.zipper
    sharing type ZO3.L.C.cat = A.Z3.cat
    sharing type ZO3.L.lens = ZO1.L.lens
    structure ZO4 : ZIPPER4_OPTICS
    sharing type ZO4.zipper = A.Z4.zipper
    sharing type ZO4.L.C.cat = A.Z4.cat
    sharing type ZO4.L.lens = ZO1.L.lens
  ) : ALTERNATING_ZIPPERS4 =
struct

open A
structure L = ZO1.L
structure Z1 = Zipper4(structure ZM = A.Z1; structure ZO = ZO1)
structure Z2 = Zipper4(structure ZM = A.Z2; structure ZO = ZO2)
structure Z3 = Zipper4(structure ZM = A.Z3; structure ZO = ZO3)
structure Z4 = Zipper4(structure ZM = A.Z4; structure ZO = ZO4)

end