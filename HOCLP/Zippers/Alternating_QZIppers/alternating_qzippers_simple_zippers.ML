(*  Title:      HOCLP/alternating_qzippers_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_QZippers_QNodes_Base_Args_Simple_Zippers(
    structure A1 : LAZY_IARROW_BASE
    structure A2 : LAZY_IARROW_BASE
    structure A3 : LAZY_IARROW_BASE
    structure A4 : LAZY_IARROW_BASE
    structure Z1 : ZIPPER
    where type ('i, 'a) content = 'a
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A1.cat
    structure Z2 : ZIPPER
    where type ('i, 'a) content = 'a
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A2.cat
    structure Z3 : ZIPPER
    where type ('i, 'a) content = 'a
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A3.cat
    structure Z4 : ZIPPER
    where type ('i, 'a) content = 'a
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A4.cat
    type ('i, 'a, 'b, 'c, 'd) ncontent1 (*content for node1*)
    type ('i, 'a, 'b, 'c, 'd) ncontent2 (*content for node2*)
    type ('i, 'a, 'b, 'c, 'd) ncontent3 (*content for node3*)
    type ('i, 'a, 'b, 'c, 'd) ncontent4 (*content for node4*)
  ) :
  sig
    structure AC : ALTERNATING_QCONTAINERS
    (* where type ('i, 'a, 'b, 'c, 'd) containeri = ('i, 'a, 'b, 'c, 'd) Zi.container *)
    include ALTERNATING_QZIPPERS_QNODES_BASE_ARGS
    where type ('i, 'a, 'b, 'c, 'd) N1.content =
      ('i, 'a, ('i, 'b, 'c, 'd, 'a) AC.acontainer2, 'c, 'd) ncontent1
    where type ('i, 'a, 'b, 'c, 'd) N2.content =
      ('i, 'a, ('i, 'b, 'c, 'd, 'a) AC.acontainer3, 'c, 'd) ncontent2
    where type ('i, 'a, 'b, 'c, 'd) N3.content =
      ('i, 'a, ('i, 'b, 'c, 'd, 'a) AC.acontainer4, 'c, 'd) ncontent3
    where type ('i, 'a, 'b, 'c, 'd) N4.content =
      ('i, 'a, ('i, 'b, 'c, 'd, 'a) AC.acontainer1, 'c, 'd) ncontent4
    (* where ('i, 'a, 'b, 'c, 'd) Zi.zcontext = ('i, ('i, 'a, 'b, 'c, 'd) Ni.node) Zi.zcontext *)
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) Z1.cat
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) Z2.cat
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) Z3.cat
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) Z4.cat
  end
  =
struct

structure N1 = QNode(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent1
  type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, 'b) Z2.Init.move
)
structure N2 = QNode(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent2
  type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, 'b) Z3.Init.move
)
structure N3 = QNode(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent3
  type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, 'b) Z4.Init.move
)
structure N4 = QNode(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent4
  type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, 'b) Z1.Init.move
)

structure Z1 = QZipper_Zipper(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) N1.node; structure Z = Z1)
structure Z2 = QZipper_Zipper(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) N2.node; structure Z = Z2)
structure Z3 = QZipper_Zipper(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) N3.node; structure Z = Z3)
structure Z4 = QZipper_Zipper(
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) N4.node; structure Z = Z4)

structure AC = Alternating_QContainers(
  type ('i, 'a, 'b, 'c, 'd) container1 = ('i, 'a, 'b, 'c, 'd) Z1.container
  type ('i, 'a, 'b, 'c, 'd) container2 = ('i, 'a, 'b, 'c, 'd) Z2.container
  type ('i, 'a, 'b, 'c, 'd) container3 = ('i, 'a, 'b, 'c, 'd) Z3.container
  type ('i, 'a, 'b, 'c, 'd) container4 = ('i, 'a, 'b, 'c, 'd) Z4.container
)

structure Base =
struct
  type ('i, 'a, 'b, 'c, 'd) inst1 = 'a
  type ('i, 'a, 'b, 'c, 'd) inst3 = 'c
  type ('i, 'a, 'b, 'c, 'd) inst4 = 'd
end
structure Base1 =
struct open Base; type ('i, 'a, 'b, 'c, 'd) inst2 = ('i, 'b, 'c, 'd, 'a) AC.acontainer2 end
structure Base2 =
struct open Base; type ('i, 'a, 'b, 'c, 'd) inst2 = ('i, 'b, 'c, 'd, 'a) AC.acontainer3 end
structure Base3 =
struct open Base; type ('i, 'a, 'b, 'c, 'd) inst2 = ('i, 'b, 'c, 'd, 'a) AC.acontainer4 end
structure Base4 =
struct open Base; type ('i, 'a, 'b, 'c, 'd) inst2 = ('i, 'b, 'c, 'd, 'a) AC.acontainer1 end
structure Z1 = Instantiate_QZipper(open Base1; structure Z = Z1)
structure Z2 = Instantiate_QZipper(open Base2; structure Z = Z2)
structure Z3 = Instantiate_QZipper(open Base3; structure Z = Z3)
structure Z4 = Instantiate_QZipper(open Base4; structure Z = Z4)
structure N1 = Instantiate_QNode(open Base1; structure N = N1)
structure N2 = Instantiate_QNode(open Base2; structure N = N2)
structure N3 = Instantiate_QNode(open Base3; structure N = N3)
structure N4 = Instantiate_QNode(open Base4; structure N = N4)

structure N1 = Replace_QNode_Content_Next(
  structure N = N1
  type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N.content
  val ncontent = I
  val dest_ncontent = I
  type ('i, 'a, 'b, 'c, 'd) nnext =
    ('i, unit, ('i, 'b, 'c, 'd, 'a) Z2.container) Z2.Init.move
  fun nnext x = Z2.Init.comp (A2.arr AC.dest_acontainer2) x
  fun dest_nnext x = Z2.Init.comp (A2.arr AC.acontainer2) x
)
structure N2 = Replace_QNode_Content_Next(
  structure N = N2
  type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N.content
  val ncontent = I
  val dest_ncontent = I
  type ('i, 'a, 'b, 'c, 'd) nnext =
    ('i, unit, ('i, 'b, 'c, 'd, 'a) Z3.container) Z3.Init.move
  fun nnext x = Z3.Init.comp (A3.arr AC.dest_acontainer3) x
  fun dest_nnext x = Z3.Init.comp (A3.arr AC.acontainer3) x
)
structure N3 = Replace_QNode_Content_Next(
  structure N = N3
  type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N.content
  val ncontent = I
  val dest_ncontent = I
  type ('i, 'a, 'b, 'c, 'd) nnext =
    ('i, unit, ('i, 'b, 'c, 'd, 'a) Z4.container) Z4.Init.move
  fun nnext x = Z4.Init.comp (A4.arr AC.dest_acontainer4) x
  fun dest_nnext x = Z4.Init.comp (A4.arr AC.acontainer4) x
)
structure N4 = Replace_QNode_Content_Next(
  structure N = N4
  type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N.content
  val ncontent = I
  val dest_ncontent = I
  type ('i, 'a, 'b, 'c, 'd) nnext =
    ('i, unit, ('i, 'b, 'c, 'd, 'a) Z1.container) Z1.Init.move
  fun nnext x = Z1.Init.comp (A1.arr AC.dest_acontainer1) x
  fun dest_nnext x = Z1.Init.comp (A1.arr AC.acontainer1) x
)

end