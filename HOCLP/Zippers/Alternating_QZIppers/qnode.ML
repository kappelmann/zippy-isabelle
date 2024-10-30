(*  Title:      HOCLP/qnode.ML
    Author:     Kevin Kappelmann
*)
signature QNODE =
sig
  type ('i, 'a, 'b, 'c, 'd) content
  type ('i, 'a, 'b, 'c, 'd) next
  type ('i, 'a, 'b, 'c, 'd) node

  val node : ('i, 'a, 'b, 'c, 'd) content -> ('i, 'a, 'b, 'c, 'd) next -> ('i, 'a, 'b, 'c, 'd) node
  val dest_node : ('i, 'a, 'b, 'c, 'd) node ->
    {content : ('i, 'a, 'b, 'c, 'd) content, next : ('i, 'a, 'b, 'c, 'd) next}

  val content : unit -> (('i, 'a, 'b, 'c, 'd) node, ('i, 'a, 'b, 'c, 'd) content,
    ('i, 'a, 'b, 'c, 'd) node, ('i, 'a, 'b, 'c, 'd) content) SLens.lens
  val next : unit -> (('i, 'a, 'b, 'c, 'd) node, ('i, 'a, 'b, 'c, 'd) next,
    ('i, 'a, 'b, 'c, 'd) node, ('i, 'a, 'b, 'c, 'd) next) SLens.lens

  val get_content : ('i, 'a, 'b, 'c, 'd) node -> ('i, 'a, 'b, 'c, 'd) content
  val get_next : ('i, 'a, 'b, 'c, 'd) node -> ('i, 'a, 'b, 'c, 'd) next

  val map_content : (('i, 'a, 'b, 'c, 'd) content -> ('i, 'a, 'b, 'c, 'd) content) ->
    ('i, 'a, 'b, 'c, 'd) node -> ('i, 'a, 'b, 'c, 'd) node
  val map_next : (('i, 'a, 'b, 'c, 'd) next -> ('i, 'a, 'b, 'c, 'd) next) ->
    ('i, 'a, 'b, 'c, 'd) node -> ('i, 'a, 'b, 'c, 'd) node
end

functor QNode(type ('i, 'a, 'b, 'c, 'd) content; type ('i, 'a, 'b, 'c, 'd) next) : QNODE =
struct

type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content
type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) next
datatype ('i, 'a, 'b, 'c, 'd) node = Node of
  {content : ('i, 'a, 'b, 'c, 'd) content, next : ('i, 'a, 'b, 'c, 'd) next}

fun node content next = Node {content = content, next = next}
fun dest_node (Node node) = node

fun get_content (Node {content, ...}) = content
fun get_next (Node {next, ...}) = next

fun map_content f (Node {content, next}) = Node {content = f content, next = next}
fun map_next f (Node {content, next}) = Node {content = content, next = f next}

fun content _ = SLens.lens get_content (uncurry map_content)
fun next _ = SLens.lens get_next (uncurry map_next)

end
