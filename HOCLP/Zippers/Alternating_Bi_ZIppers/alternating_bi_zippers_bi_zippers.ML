(*  Title:      HOCLP/alternating_bi_zippers_bi_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_Bi_Zippers_Bi_Nodes_Base_Args_Bi_Zippers(
    structure Z1 : BI_ZIPPER
    structure Z2 : BI_ZIPPER
    structure AC : ALTERNATING_BI_CONTAINERS
    sharing type AC.container1 = Z1.container
    sharing type AC.container2 = Z2.container
    type ('i, 'a, 'b) ncontent1 (*content for node1*)
    type ('i, 'a, 'b) ncontent2 (*content for node2*)
    val ncontent1 : ('i, 'a, ('i, 'b, 'a) AC.acontainer2) Z1.content -> ('i, 'a, 'b) ncontent1
    val ncontent2 : ('i, 'a, ('i, 'b, 'a) AC.acontainer1) Z2.content -> ('i, 'a, 'b) ncontent2
    val next1 : ('i, 'a, ('i, 'b, 'a) AC.acontainer2) Z1.content ->
      ('i, ('i, 'b, ('i, 'a, 'b) AC.acontainer1) Z2.container) Z2.mt
    val next2 : ('i, 'a, ('i, 'b, 'a) AC.acontainer1) Z2.content ->
      ('i, ('i, 'b, ('i, 'a, 'b) AC.acontainer2) Z1.container) Z1.mt
    val content1 : ('i, 'a, 'b) ncontent1 ->
      ('i, ('i, 'b, ('i, 'a, 'b) AC.acontainer1) Z2.container) Z2.mt ->
      ('i, 'a, ('i, 'b, 'a) AC.acontainer2) Z1.content
    val content2 : ('i, 'a, 'b) ncontent2 ->
      ('i, ('i, 'b, ('i, 'a, 'b) AC.acontainer2) Z1.container) Z1.mt ->
      ('i, 'a, ('i, 'b, 'a) AC.acontainer1) Z2.content
  ) : ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS =
struct
    structure BZ1 = Instantiate_Bi_Zipper(
    structure Z = Z1
    type ('i, 'a, 'b) inst1 = 'a
    type ('i, 'a, 'b) inst2 = ('i, 'b, 'a) AC.acontainer2
  )
  structure BZ2 = Instantiate_Bi_Zipper(
    structure Z = Z2
    type ('i, 'a, 'b) inst1 = 'a
    type ('i, 'a, 'b) inst2 = ('i, 'b, 'a) AC.acontainer1
  )
  structure N1 = Bi_Node(
    type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent1
    type ('i, 'a, 'b) next = ('i, ('i, 'b, 'a) BZ2.container) BZ2.Init.mt
  )
  structure N2 = Bi_Node(
    type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent2
    type ('i, 'a, 'b) next = ('i, ('i, 'b, 'a) BZ1.container) BZ1.Init.mt
  )

  structure BZ1 = Replace_Bi_Zipper_Content(
    structure Z = BZ1
    type ('i, 'a, 'b) ncontent = ('i, 'a, 'b) N1.node
    fun ncontent x = N1.node (ncontent1 x) (next1 x)
    fun dest_ncontent x = N1.dest_node x |> (fn {content, next} => content1 content next)
  )
  structure BZ2 = Replace_Bi_Zipper_Content(
    structure Z = BZ2
    type ('i, 'a, 'b) ncontent = ('i, 'a, 'b) N2.node
    fun ncontent x = N2.node (ncontent2 x) (next2 x)
    fun dest_ncontent x = N2.dest_node x |> (fn {content, next} => content2 content next)
  )
end
