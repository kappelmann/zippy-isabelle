(*  Title:      HOCLP/alternating_linked_containers.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_LINKED_CONTAINERS =
sig
  structure N1 : NODES
  structure N2 : NODES

  type ('c1, 'c2) anodes1
  type ('c1, 'c2) anodes2
  type ('c1, 'c2) node1 = ('c1, ('c1, 'c2) anodes2) N1.node
  type ('c1, 'c2) node2 = ('c2, ('c1, 'c2) anodes1) N2.node
  type ('c1, 'c2) nodes1 = ('c1, ('c1, 'c2) anodes2) N1.nodes
  type ('c1, 'c2) nodes2 = ('c2, ('c1, 'c2) anodes1) N2.nodes

  val anodes1 : ('c1, 'c2) nodes1 -> ('c1, 'c2) anodes1
  val get_nodes1 : ('c1, 'c2) anodes1 -> ('c1, 'c2) nodes1
  val map_nodes1: (('c1, 'c2) nodes1 -> ('d1, 'd2) nodes1) ->
    ('c1, 'c2) anodes1 -> ('d1, 'd2) anodes1

  val anodes2 : ('c1, 'c2) nodes2 -> ('c1, 'c2) anodes2
  val get_nodes2 : ('c1, 'c2) anodes2 -> ('c1, 'c2) nodes2
  val map_nodes2: (('c1, 'c2) nodes2 -> ('d1, 'd2) nodes2) ->
    ('c1, 'c2) anodes2 -> ('d1, 'd2) anodes2

  val nodes1 : unit ->
    (('d1, 'd2) anodes1, ('d1, 'd2) nodes1, ('c1, 'c2) anodes1, ('c1, 'c2) nodes1) SLens.lens
  val nodes2 : unit ->
    (('d1, 'd2) anodes2, ('d1, 'd2) nodes2, ('c1, 'c2) anodes2, ('c1, 'c2) nodes2) SLens.lens

end

functor Alternating_Linked_Containers(structure N1 : NODES; structure N2 : NODES)
  : ALTERNATING_LINKED_CONTAINERS =
struct

structure N1 = N1
structure N2 = N2

datatype ('c1, 'c2) anodes1 = Anodes1 of ('c1, ('c1, 'c2) anodes2) N1.nodes
and ('c1, 'c2) anodes2 = Anodes2 of ('c2, ('c1, 'c2) anodes1) N2.nodes

type ('c1, 'c2) node1 = ('c1, ('c1, 'c2) anodes2) N1.node
type ('c1, 'c2) node2 = ('c2, ('c1, 'c2) anodes1) N2.node
type ('c1, 'c2) nodes1 = ('c1, ('c1, 'c2) anodes2) N1.nodes
type ('c1, 'c2) nodes2 = ('c2, ('c1, 'c2) anodes1) N2.nodes

val anodes1 = Anodes1
fun get_nodes1 (Anodes1 n) = n
fun map_nodes1 f (Anodes1 n) = anodes1 (f n)

val anodes2 = Anodes2
fun get_nodes2 (Anodes2 n) = n
fun map_nodes2 f (Anodes2 n) = anodes2 (f n)

fun nodes1 _ = SLens.lens get_nodes1 (uncurry map_nodes1)
fun nodes2 _ = SLens.lens get_nodes2 (uncurry map_nodes2)

end
