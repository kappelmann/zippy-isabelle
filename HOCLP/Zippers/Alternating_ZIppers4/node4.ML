(*  Title:      HOCLP/node4.ML
    Author:     Kevin Kappelmann
*)
signature NODE4 =
sig
  structure L : LENS
  type ('p1, 'a1, 'a2, 'a3, 'a4) content
  type ('p1, 'a1, 'a2, 'a3, 'a4) next
  type ('p1, 'a1, 'a2, 'a3, 'a4) node

  val node : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) content * ('p1, 'a1, 'a2, 'a3, 'a4) next,
    ('p1, 'a1, 'a2, 'a3, 'a4) node) L.C.cat

  val content : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node, ('p1, 'a1, 'a2, 'a3, 'a4) content) L.slens
  val next : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node, ('p1, 'a1, 'a2, 'a3, 'a4) next) L.slens
  val get_content :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node, ('p1, 'a1, 'a2, 'a3, 'a4) content) L.getter
  val get_next :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node, ('p1, 'a1, 'a2, 'a3, 'a4) next) L.getter
  val map_content :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node, ('p1, 'a1, 'a2, 'a3, 'a4) content) L.smodifier
  val map_next :
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node, ('p1, 'a1, 'a2, 'a3, 'a4) next) L.smodifier
end

functor Node4(
    type ('p1, 'a1, 'a2, 'a3, 'a4) content
    type ('p1, 'a1, 'a2, 'a3, 'a4) next
  ) : NODE4 where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat =
struct

structure L = SLens

type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) next
datatype ('p1, 'a1, 'a2, 'a3, 'a4) node = Node of
  {content : ('p1, 'a1, 'a2, 'a3, 'a4) content, next : ('p1, 'a1, 'a2, 'a3, 'a4) next}

fun node (content, next) = Node {content = content, next = next}

fun get_content (Node {content,...}) = content
fun get_next (Node {next,...}) = next

fun map_content (f, Node {content, next}) = Node {content = f content, next = next}
fun map_next (f, Node {content, next}) = Node {content = content, next = f next}

fun content _ = L.lens get_content map_content
fun next _ = L.lens get_next map_next

end

signature LIFT_NODE4 =
sig
  structure N : NODE4
  include NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) N.next
  where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) N.node
end

functor Lift_Node4(
    structure AF : ARROW
    structure N : NODE4
    sharing type N.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AT.cat
    val lift : ('p1, 'a, 'b) AF.cat -> ('p1, 'a, 'b) AT.cat
  ) : LIFT_NODE4 =
struct

structure N = N
structure L = L

type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N.content
type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) N.next
type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) N.node

fun node x = x |> lift N.node
fun node_lens _ = L.lens_get_mk (lift (AF.&&& (N.get_content, N.get_next))) node
fun content _ = L.lens_fst (node_lens ())
fun next _ = L.lens_snd (node_lens ())
fun get_content x = x |> L.get (content ())
fun map_content x = x |> L.modify (content ())
fun get_next x = x |> L.get (next ())
fun map_next x = x |> L.modify (next ())

end
