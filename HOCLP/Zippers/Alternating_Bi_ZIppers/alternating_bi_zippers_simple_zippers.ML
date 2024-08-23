(*  Title:      HOCLP/alternating_bi_zippers_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_Bi_Zippers_Bi_Nodes_Base_Args_Simple_Zippers(
    structure A1 : IARROW_BASE
    structure A2 : IARROW_BASE
    structure Z1 : ZIPPER
    where type ('i, 'a) content = 'a
    sharing type Z1.C.cat = A1.cat
    structure Z2 : ZIPPER
    where type ('i, 'a) content = 'a
    sharing type Z2.C.cat = A2.cat
    type ('i, 'a, 'b) ncontent1 (*content for node1*)
    type ('i, 'a, 'b) ncontent2 (*content for node2*)
  ) :
  sig
    structure AC : ALTERNATING_BI_CONTAINERS
    (* where type ('i, 'a, 'b) container1 = ('i, 'a, 'b) BZ1.container *)
    (* where type ('i, 'a, 'b) container2 = ('i, 'a, 'b) BZ2.container *)
    include ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS
    where type ('i, 'a, 'b) N1.content = ('i, 'a, ('i, 'b, 'a) AC.acontainer2) ncontent1
    where type ('i, 'a, 'b) N2.content = ('i, 'a, ('i, 'b, 'a) AC.acontainer1) ncontent2
    (* where ('i, 'a, 'b) BZ1.zcontext = ('i, ('i, 'a, 'b) N1.node) Z1.zcontext *)
    (* where ('i, 'a, 'b) BZ1.zipper = ('i, ('i, 'a, 'b) N1.node) Z1.zipper *)
    (* where ('i, 'a, 'b) BZ1.container = ('i, ('i, 'a, 'b) N1.node) Z1.container *)
    (* where ('i, 'a, 'b) BZ2.zcontext = ('i, ('i, 'a, 'b) N2.node) Z2.zcontext *)
    (* where ('i, 'a, 'b) BZ2.zipper = ('i, ('i, 'a, 'b) N2.node) Z2.zipper *)
    (* where ('i, 'a, 'b) BZ2.container = ('i, ('i, 'a, 'b) N1.node) Z2.container *)
    where type ('i, 'j, 'a, 'b) BZ1.C.cat = ('i, 'j, 'a, 'b) Z1.C.cat
    where type ('i, 'j, 'a, 'b) BZ2.C.cat = ('i, 'j, 'a, 'b) Z2.C.cat
  end
  =
struct

structure N1 = Bi_Node(
  type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent1
  type ('i, 'a, 'b) next = ('i, 'i, unit, 'b) Z2.Init.C.cat
)
structure N2 = Bi_Node(
  type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent2
  type ('i, 'a, 'b) next = ('i, 'i, unit, 'b) Z1.Init.C.cat
)

structure BZ1 = Bi_Zipper_Zipper(type ('i, 'a, 'b) content = ('i, 'a, 'b) N1.node; structure Z = Z1)
structure BZ2 = Bi_Zipper_Zipper(type ('i, 'a, 'b) content = ('i, 'a, 'b) N2.node; structure Z = Z2)

structure AC = Alternating_Bi_Containers(
  type ('i, 'a, 'b) container1 = ('i, 'a, 'b) BZ1.container
  type ('i, 'a, 'b) container2 = ('i, 'a, 'b) BZ2.container
)
structure BZ1 = Instantiate_Bi_Zipper(
  structure Z = BZ1
  type ('i, 'a, 'b) inst1 = 'a
  type ('i, 'a, 'b) inst2 = ('i, 'b, 'a) AC.acontainer2
)
structure BZ2 = Instantiate_Bi_Zipper(
  structure Z = BZ2
  type ('i, 'a, 'b) inst1 = 'a
  type ('i, 'a, 'b) inst2 = ('i, 'b, 'a) AC.acontainer1
)
structure N1 = Instantiate_Bi_Node(
  structure N = N1
  type ('i, 'a, 'b) cinst = 'a
  type ('i, 'a, 'b) ninst = ('i, 'b, 'a) AC.acontainer2
)
structure N2 = Instantiate_Bi_Node(
  structure N = N2
  type ('i, 'a, 'b) cinst = 'a
  type ('i, 'a, 'b) ninst = ('i, 'b, 'a) AC.acontainer1
)

structure N1 = Replace_Bi_Node_Content_Next(
  structure N = N1
  type ('i, 'a, 'b) ncontent = ('i, 'a, 'b) N.content
  val ncontent = I
  val dest_ncontent = I
  type ('i, 'a, 'b) nnext = ('i, 'i, unit, ('i, 'b, 'a) BZ2.container) BZ2.Init.C.cat
  fun nnext x = BZ2.Init.C.comp (A2.arr AC.dest_acontainer2) x
  fun dest_nnext x = BZ2.Init.C.comp (A2.arr AC.acontainer2) x
)
structure N2 = Replace_Bi_Node_Content_Next(
  structure N = N2
  type ('i, 'a, 'b) ncontent = ('i, 'a, 'b) N.content
  val ncontent = I
  val dest_ncontent = I
  type ('i, 'a, 'b) nnext = ('i, 'i, unit, ('i, 'b, 'a) BZ1.container) BZ1.Init.C.cat
  fun nnext x = BZ1.Init.C.comp (A1.arr AC.dest_acontainer1) x
  fun dest_nnext x = BZ1.Init.C.comp (A1.arr AC.acontainer1) x
)

end