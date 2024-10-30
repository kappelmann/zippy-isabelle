(*  Title:      HOCLP/replace_alternating_qzippers_zipper.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Alternating_QZippers_Zipper(
    structure A1 : LAZY_IARROW_BASE
    structure A2 : LAZY_IARROW_BASE
    structure A3 : LAZY_IARROW_BASE
    structure A4 : LAZY_IARROW_BASE
    structure DA1 : LAZY_IARROW_BASE
    structure DA2 : LAZY_IARROW_BASE
    structure DA3 : LAZY_IARROW_BASE
    structure DA4 : LAZY_IARROW_BASE
    structure UA1 : LAZY_IARROW_BASE
    structure UA2 : LAZY_IARROW_BASE
    structure UA3 : LAZY_IARROW_BASE
    structure UA4 : LAZY_IARROW_BASE
    structure AZ : ALTERNATING_QZIPPERS
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) A1.T.lcat
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) A2.T.lcat
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) A3.T.lcat
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) A4.T.lcat
    where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) DA1.T.lcat
    where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) DA2.T.lcat
    where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) DA3.T.lcat
    where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) DA4.T.lcat
    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) UA1.T.lcat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) UA2.T.lcat
    where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) UA3.T.lcat
    where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) UA4.T.lcat
    type ('i, 'a, 'b, 'c, 'd) nzipper1
    val nzipper1 : ('i, 'a, 'b, 'c, 'd) AZ.Z1.zipper -> ('i, 'a, 'b, 'c, 'd) nzipper1
    val dest_nzipper1 : ('i, 'a, 'b, 'c, 'd) nzipper1 -> ('i, 'a, 'b, 'c, 'd) AZ.Z1.zipper
    type ('i, 'a, 'b, 'c, 'd) nzipper2
    val nzipper2 : ('i, 'a, 'b, 'c, 'd) AZ.Z2.zipper -> ('i, 'a, 'b, 'c, 'd) nzipper2
    val dest_nzipper2 : ('i, 'a, 'b, 'c, 'd) nzipper2 -> ('i, 'a, 'b, 'c, 'd) AZ.Z2.zipper
    type ('i, 'a, 'b, 'c, 'd) nzipper3
    val nzipper3 : ('i, 'a, 'b, 'c, 'd) AZ.Z3.zipper -> ('i, 'a, 'b, 'c, 'd) nzipper3
    val dest_nzipper3 : ('i, 'a, 'b, 'c, 'd) nzipper3 -> ('i, 'a, 'b, 'c, 'd) AZ.Z3.zipper
    type ('i, 'a, 'b, 'c, 'd) nzipper4
    val nzipper4 : ('i, 'a, 'b, 'c, 'd) AZ.Z4.zipper -> ('i, 'a, 'b, 'c, 'd) nzipper4
    val dest_nzipper4 : ('i, 'a, 'b, 'c, 'd) nzipper4 -> ('i, 'a, 'b, 'c, 'd) AZ.Z4.zipper
  ) :
    ALTERNATING_QZIPPERS
    where type ('i, 'a, 'b, 'c, 'd) Z1.content = ('i, 'a, 'b, 'c, 'd) AZ.Z1.content
    where type ('i, 'a, 'b, 'c, 'd) Z1.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z1.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z1.zipper = ('i, 'a, 'b, 'c, 'd) nzipper1
    where type ('i, 'a, 'b, 'c, 'd) Z1.container = ('i, 'a, 'b, 'c, 'd) AZ.Z1.container
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AZ.Z1.cat
    where type ('i, 'a, 'b, 'c, 'd) Z2.content = ('i, 'a, 'b, 'c, 'd) AZ.Z2.content
    where type ('i, 'a, 'b, 'c, 'd) Z2.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z2.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z2.zipper = ('i, 'a, 'b, 'c, 'd) nzipper2
    where type ('i, 'a, 'b, 'c, 'd) Z2.container = ('i, 'a, 'b, 'c, 'd) AZ.Z2.container
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) AZ.Z2.cat
    where type ('i, 'a, 'b, 'c, 'd) Z3.content = ('i, 'a, 'b, 'c, 'd) AZ.Z3.content
    where type ('i, 'a, 'b, 'c, 'd) Z3.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z3.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z3.zipper = ('i, 'a, 'b, 'c, 'd) nzipper3
    where type ('i, 'a, 'b, 'c, 'd) Z3.container = ('i, 'a, 'b, 'c, 'd) AZ.Z3.container
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) AZ.Z3.cat
    where type ('i, 'a, 'b, 'c, 'd) Z4.content = ('i, 'a, 'b, 'c, 'd) AZ.Z4.content
    where type ('i, 'a, 'b, 'c, 'd) Z4.zcontext = ('i, 'a, 'b, 'c, 'd) AZ.Z4.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z4.zipper = ('i, 'a, 'b, 'c, 'd) nzipper4
    where type ('i, 'a, 'b, 'c, 'd) Z4.container = ('i, 'a, 'b, 'c, 'd) AZ.Z4.container
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) AZ.Z4.cat
    where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) AZ.Down1.cat
    where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) AZ.Down2.cat
    where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) AZ.Down3.cat
    where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) AZ.Down4.cat
    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AZ.Up1.cat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AZ.Up2.cat
    where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) AZ.Up3.cat
    where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) AZ.Up4.cat
  =
struct

structure Z1 = Replace_QZipper_Zipper(
  structure A = A1
  structure Z = AZ.Z1
  type ('i, 'a, 'b, 'c, 'd) nzipper = ('i, 'a, 'b, 'c, 'd) nzipper1
  val nzipper = nzipper1
  val dest_nzipper = dest_nzipper1
)
structure Z2 = Replace_QZipper_Zipper(
  structure A = A2
  structure Z = AZ.Z2
  type ('i, 'a, 'b, 'c, 'd) nzipper = ('i, 'a, 'b, 'c, 'd) nzipper2
  val nzipper = nzipper2
  val dest_nzipper = dest_nzipper2
)
structure Z3 = Replace_QZipper_Zipper(
  structure A = A3
  structure Z = AZ.Z3
  type ('i, 'a, 'b, 'c, 'd) nzipper = ('i, 'a, 'b, 'c, 'd) nzipper3
  val nzipper = nzipper3
  val dest_nzipper = dest_nzipper3
)
structure Z4 = Replace_QZipper_Zipper(
  structure A = A4
  structure Z = AZ.Z4
  type ('i, 'a, 'b, 'c, 'd) nzipper = ('i, 'a, 'b, 'c, 'd) nzipper4
  val nzipper = nzipper4
  val dest_nzipper = dest_nzipper4
)

structure Down1 = Replace_QMove_From_To(
  structure C = DA1
  structure M = AZ.Down1
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper1
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'b, 'c, 'd, 'a) nzipper2
  fun dest_nfrom _ = C.arr dest_nzipper1 ()
  fun nto _ = C.arr nzipper2 ()
)
structure Down2 = Replace_QMove_From_To(
  structure C = DA2
  structure M = AZ.Down2
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper2
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'b, 'c, 'd, 'a) nzipper3
  fun dest_nfrom _ = C.arr dest_nzipper2 ()
  fun nto _ = C.arr nzipper3 ()
)
structure Down3 = Replace_QMove_From_To(
  structure C = DA3
  structure M = AZ.Down3
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper3
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'b, 'c, 'd, 'a) nzipper4
  fun dest_nfrom _ = C.arr dest_nzipper3 ()
  fun nto _ = C.arr nzipper4 ()
)
structure Down4 = Replace_QMove_From_To(
  structure C = DA4
  structure M = AZ.Down4
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper4
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'b, 'c, 'd, 'a) nzipper1
  fun dest_nfrom _ = C.arr dest_nzipper4 ()
  fun nto _ = C.arr nzipper1 ()
)

structure Up1 = Replace_QMove_From_To(
  structure C = UA1
  structure M = AZ.Up1
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper1
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'd, 'a, 'b, 'c) nzipper4
  fun dest_nfrom _ = C.arr dest_nzipper1 ()
  fun nto _ = C.arr nzipper4 ()
)
structure Up2 = Replace_QMove_From_To(
  structure C = UA2
  structure M = AZ.Up2
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper2
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'd, 'a, 'b, 'c) nzipper1
  fun dest_nfrom _ = C.arr dest_nzipper2 ()
  fun nto _ = C.arr nzipper1 ()
)
structure Up3 = Replace_QMove_From_To(
  structure C = UA3
  structure M = AZ.Up3
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper3
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'd, 'a, 'b, 'c) nzipper2
  fun dest_nfrom _ = C.arr dest_nzipper3 ()
  fun nto _ = C.arr nzipper2 ()
)
structure Up4 = Replace_QMove_From_To(
  structure C = UA4
  structure M = AZ.Up4
  type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nzipper4
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'd, 'a, 'b, 'c) nzipper3
  fun dest_nfrom _ = C.arr dest_nzipper4 ()
  fun nto _ = C.arr nzipper3 ()
)
end