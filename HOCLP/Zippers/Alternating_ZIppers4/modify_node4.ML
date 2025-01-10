(*  Title:      HOCLP/modify_node4.ML
    Author:     Kevin Kappelmann
*)
functor Instantiate_Node4(
    structure N : NODE4
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst4
  ) :
    NODE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4) N.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4) N.next
    where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst1, ('p1, 'a1, 'a2, 'a3, 'a4) inst2,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst3, ('p1, 'a1, 'a2, 'a3, 'a4) inst4) N.node
  = N

functor Replace_Node4_Content_Next(
    structure A : KLEISLI_ARROW_BASE
    structure N : NODE4
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    val ncontent :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) N.content, ('p1, 'a1, 'a2, 'a3, 'a4) ncontent) A.cat
    val dest_ncontent :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) ncontent, ('p1, 'a1, 'a2, 'a3, 'a4) N.content) A.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nnext
    val nnext :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) N.next, ('p1, 'a1, 'a2, 'a3, 'a4) nnext) A.cat
    val dest_nnext :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nnext, ('p1, 'a1, 'a2, 'a3, 'a4) N.next) A.cat
  ) :
    NODE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) nnext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) N.node
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) N.L.C.cat
    where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) N.L.lens
  =
struct

structure L = N.L
type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) nnext
type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) N.node

structure SC = Semi_Category(A) open SC A

fun node x = x |> ((dest_ncontent *** dest_nnext) >>> N.node)

fun content _ = L.comp (L.lens_get_mk ncontent dest_ncontent) (N.content ())
fun next _ = L.comp (L.lens_get_mk nnext dest_nnext) (N.next ())

fun get_content x = x |> L.get (content ())
fun get_next x = x |> L.get (next ())
fun map_content x = x |> L.modify (content ())
fun map_next x = x |> L.modify (next ())

end
