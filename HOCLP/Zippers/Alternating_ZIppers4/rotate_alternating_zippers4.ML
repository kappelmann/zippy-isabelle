(*  Title:      HOCLP/rotate_alternating_zippers4.ML
    Author:     Kevin Kappelmann
*)
functor Rotate_Alternating_Zippers4(AZ : ALTERNATING_ZIPPERS4) :
  ALTERNATING_ZIPPERS4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.zipper

  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.zipper

  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.zipper

  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.zipper
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AZ.cat
  =
struct
structure M : MOVE_BASE = AZ
open M
structure L = AZ.L
structure Z1 = AZ.Z2
structure Z2 = AZ.Z3
structure Z3 = AZ.Z4
structure Z4 = AZ.Z1
structure Down1 = AZ.Down2
structure Down2 = AZ.Down3
structure Down3 = AZ.Down4
structure Down4 = AZ.Down1
structure Up1 = AZ.Up2
structure Up2 = AZ.Up3
structure Up3 = AZ.Up4
structure Up4 = AZ.Up1
end
