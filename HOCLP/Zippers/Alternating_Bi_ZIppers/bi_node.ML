(*  Title:      HOCLP/bi_node.ML
    Author:     Kevin Kappelmann
*)
signature BI_NODE =
sig
  type ('i, 'a, 'b) content
  type ('i, 'a, 'b) next
  type ('i, 'a, 'b) node

  val node : ('i, 'a, 'b) content -> ('i, 'a, 'b) next -> ('i, 'a, 'b) node
  val dest_node : ('i, 'a, 'b) node -> {content : ('i, 'a, 'b) content, next : ('i, 'a, 'b) next}

  val content : unit -> (('i, 'a, 'b) node, ('i, 'a, 'b) content, ('i, 'a, 'b) node,
    ('i, 'a, 'b) content) SLens.lens
  val next : unit -> (('i, 'a, 'b) node, ('i, 'a, 'b) next, ('i, 'a, 'b) node,
    ('i, 'a, 'b) next) SLens.lens

  val get_content : ('i, 'a, 'b) node -> ('i, 'a, 'b) content
  val get_next : ('i, 'a, 'b) node -> ('i, 'a, 'b) next

  val map_content : (('i, 'a, 'b) content -> ('i, 'a, 'b) content) -> ('i, 'a, 'b) node ->
    ('i, 'a, 'b) node
  val map_next : (('i, 'a, 'b) next -> ('i, 'a, 'b) next) -> ('i, 'a, 'b) node -> ('i, 'a, 'b) node
end

functor Bi_Node(type ('i, 'a, 'b) content; type ('i, 'a, 'b) next) : BI_NODE =
struct

type ('i, 'a, 'b) content = ('i, 'a, 'b) content
type ('i, 'a, 'b) next = ('i, 'a, 'b) next
datatype ('i, 'a, 'b) node = Node of {content : ('i, 'a, 'b) content, next : ('i, 'a, 'b) next}

fun node content next = Node {content = content, next = next}
fun dest_node (Node node) = node

fun get_content (Node {content, ...}) = content
fun get_next (Node {next, ...}) = next

fun map_content f (Node {content, next}) = Node {content = f content, next = next}
fun map_next f (Node {content, next}) = Node {content = content, next = f next}

fun content _ = SLens.lens get_content (uncurry map_content)
fun next _ = SLens.lens get_next (uncurry map_next)

end
