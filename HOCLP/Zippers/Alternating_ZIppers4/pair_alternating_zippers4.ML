(*  Title:      HOCLP/pair_alternating_zippers4.ML
    Auor:     Kevin Kappelmann
*)
signature PAIR_ALTERNATING_ZIPPERS4 =
sig
  structure AZ1 : ALTERNATING_ZIPPERS4
  structure AZ2 : ALTERNATING_ZIPPERS4
  sharing type AZ2.M.t = AZ1.M.t

  include ALTERNATING_ZIPPERS4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) AZ1.Z1.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) AZ2.Z1.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content =
    ('p1, 'a1, 'a2, 'a3, 'a4) AZ1.Z1.ZO.content * ('p1, 'a1, 'a2, 'a3, 'a4) AZ2.Z1.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext =
    ('p1, 'a1, 'a2, 'a3, 'a4) AZ1.Z1.ZO.zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) AZ2.Z1.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper =
    ('p1, 'a1, 'a2, 'a3, 'a4) AZ1.Z1.zipper * ('p1, 'a1, 'a2, 'a3, 'a4) AZ2.Z1.zipper
  where type ('p1, 'a) Z1.M.t = ('p1, 'a) AZ1.Z1.M.t
end

functor Pair_Alternating_Zippers4(
    structure AZ1 : ALTERNATING_ZIPPERS4
    structure AZ2 : ALTERNATING_ZIPPERS4
    sharing type AZ2.M.t = AZ1.M.t
    sharing type AZ2.L.lens = AZ1.L.lens
  ) : PAIR_ALTERNATING_ZIPPERS4
  =
struct

structure AZ1 = AZ1
structure AZ2 = AZ2
structure M : MOVE_BASE = AZ1
open M
structure L = AZ1.L

structure Z1 = Pair_Zipper4(
  structure Z1 = AZ1.Z1
  structure Z2 = AZ2.Z1
)
structure Z2 = Pair_Zipper4(
  structure Z1 = AZ1.Z2
  structure Z2 = AZ2.Z2
)
structure Z3 = Pair_Zipper4(
  structure Z1 = AZ1.Z3
  structure Z2 = AZ2.Z3
)
structure Z4 = Pair_Zipper4(
  structure Z1 = AZ1.Z4
  structure Z2 = AZ2.Z4
)

structure Down1 = Pair_Move4(
  structure M1 = AZ1.Down1
  structure M2 = AZ2.Down1
)
structure Down2 = Pair_Move4(
  structure M1 = AZ1.Down2
  structure M2 = AZ2.Down2
)
structure Down3 = Pair_Move4(
  structure M1 = AZ1.Down3
  structure M2 = AZ2.Down3
)
structure Down4 = Pair_Move4(
  structure M1 = AZ1.Down4
  structure M2 = AZ2.Down4
)

structure Up1 = Pair_Move4(
  structure M1 = AZ1.Up1
  structure M2 = AZ2.Up1
)
structure Up2 = Pair_Move4(
  structure M1 = AZ1.Up2
  structure M2 = AZ2.Up2
)
structure Up3 = Pair_Move4(
  structure M1 = AZ1.Up3
  structure M2 = AZ2.Up3
)
structure Up4 = Pair_Move4(
  structure M1 = AZ1.Up4
  structure M2 = AZ2.Up4
)

end
