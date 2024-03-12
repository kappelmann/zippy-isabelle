(*  Title:      HOCLP/node.ML
    Author:     Kevin Kappelmann
*)
signature NODE =
sig
  type ('c, 'n) node

  val node : 'c -> 'n -> ('c, 'n) node
  val dest_node : ('c, 'n) node -> {content : 'c, next : 'n}

  val get_content : ('c, 'n) node -> 'c
  val get_next : ('c, 'n) node -> 'n

  val map_content : ('c1 -> 'c2) -> ('c1, 'n) node -> ('c2, 'n) node
  val map_next : ('n1 -> 'n2) -> ('c, 'n1) node -> ('c, 'n2) node

  val content : unit -> (('c2, 'n) node, 'c2, ('c1, 'n) node, 'c1) SLens.lens
  val next : unit -> (('c, 'n2) node, 'n2, ('c, 'n1) node, 'n1) SLens.lens
end

structure Node : NODE =
struct

datatype ('c, 'n) node = Node of {content : 'c, next : 'n}

fun node content next = Node {content = content, next = next}
fun dest_node (Node node) = node

fun get_content (Node {content, ...}) = content
fun get_next (Node {next, ...}) = next

fun map_content f (Node {content, next}) = Node {content = f content, next = next}
fun map_next f (Node {content, next}) = Node {content = content, next = f next}

fun content _ = SLens.lens get_content (uncurry map_content)
fun next _ = SLens.lens get_next (uncurry map_next)

end

signature NODES =
sig
  structure N : NODE
  structure C : CONTAINER

  type ('c, 'n) node = ('c, 'n) N.node
  type ('c, 'n) nodes = ('c, 'n) node C.container
end

functor Nodes(structure N : NODE; structure C : CONTAINER) : NODES =
struct

structure N = N
structure C = C

type ('c, 'n) node = ('c, 'n) N.node
type ('c, 'n) nodes = ('c, 'n) node C.container

end
