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
    structure A : LAZY_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) content
    type ('p1, 'a1, 'a2, 'a3, 'a4) next
  ) : NODE4 =
struct

structure L = L

type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) next
datatype ('p1, 'a1, 'a2, 'a3, 'a4) node = Node of
  {content : ('p1, 'a1, 'a2, 'a3, 'a4) content, next : ('p1, 'a1, 'a2, 'a3, 'a4) next}

open A
fun node _ = arr (fn (content, next) => Node {content = content, next = next})
  |> Lazy_Cat_Util.unlift
fun node_lens _ = L.lens_get_mk (A.arr (fn Node {content, next} => (content, next))) node
fun content _ = L.lens_fst (node_lens ())
fun next _ = L.lens_snd (node_lens ())
fun get_content _ = L.get (content ())
  |> Lazy_Cat_Util.unlift
fun map_content _ = L.modify (content ())
  |> Lazy_Cat_Util.unlift
fun get_next _ = L.get (next ())
  |> Lazy_Cat_Util.unlift
fun map_next _ = L.modify (next ())
  |> Lazy_Cat_Util.unlift

end
