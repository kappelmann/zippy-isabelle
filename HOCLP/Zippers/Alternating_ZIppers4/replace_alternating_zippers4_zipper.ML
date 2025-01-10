(*  Title:      HOCLP/replace_alternating_zippers4_zipper.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Alternating_Zippers4_Zipper(
    structure AZ : ALTERNATING_ZIPPERS4
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
    val nzipper1 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.zipper,
      ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1) AZ.cat
    val dest_nzipper1 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1,
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.zipper) AZ.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
    val nzipper2 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.zipper,
      ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2) AZ.cat
    val dest_nzipper2 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2,
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.zipper) AZ.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
    val nzipper3 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.zipper,
      ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3) AZ.cat
    val dest_nzipper3 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3,
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.zipper) AZ.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
    val nzipper4 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.zipper,
      ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4) AZ.cat
    val dest_nzipper4 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4,
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.zipper) AZ.cat
  ) :
    ALTERNATING_ZIPPERS4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.zcontext =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.zcontext =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container =
      ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
    where type ('p1, 'a) Z1.M.t = ('p1, 'a) AZ.Z1.M.t
  =
struct

structure M : MOVE_BASE = AZ
open M
structure L = AZ.L

structure Z1 = Replace_Zipper4_Zipper(
  structure Z = AZ.Z1
  type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
  val nzipper = nzipper1
  val dest_nzipper = dest_nzipper1
)
structure Z2 = Replace_Zipper4_Zipper(
  structure Z = AZ.Z2
  type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
  val nzipper = nzipper2
  val dest_nzipper = dest_nzipper2
)
structure Z3 = Replace_Zipper4_Zipper(
  structure Z = AZ.Z3
  type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
  val nzipper = nzipper3
  val dest_nzipper = dest_nzipper3
)
structure Z4 = Replace_Zipper4_Zipper(
  structure Z = AZ.Z4
  type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
  val nzipper = nzipper4
  val dest_nzipper = dest_nzipper4
)

structure Down1 = Replace_Move4_From_To(
  structure M = AZ.Down1
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
  val dest_nfrom = dest_nzipper1
  val nto = nzipper2
)
structure Down2 = Replace_Move4_From_To(
  structure M = AZ.Down2
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
  val dest_nfrom = dest_nzipper2
  val nto = nzipper3
)
structure Down3 = Replace_Move4_From_To(
  structure M = AZ.Down3
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
  val dest_nfrom = dest_nzipper3
  val nto = nzipper4
)
structure Down4 = Replace_Move4_From_To(
  structure M = AZ.Down4
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
  val dest_nfrom = dest_nzipper4
  val nto = nzipper1
)

structure Up1 = Replace_Move4_From_To(
  structure M = AZ.Up1
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
  val dest_nfrom = dest_nzipper1
  val nto = nzipper4
)
structure Up2 = Replace_Move4_From_To(
  structure M = AZ.Up2
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper1
  val dest_nfrom = dest_nzipper2
  val nto = nzipper1
)
structure Up3 = Replace_Move4_From_To(
  structure M = AZ.Up3
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper2
  val dest_nfrom = dest_nzipper3
  val nto = nzipper2
)
structure Up4 = Replace_Move4_From_To(
  structure M = AZ.Up4
  type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper4
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper3
  val dest_nfrom = dest_nzipper4
  val nto = nzipper3
)

end