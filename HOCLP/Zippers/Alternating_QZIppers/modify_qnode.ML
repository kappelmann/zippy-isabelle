(*  Title:      HOCLP/modify_qnode.ML
    Author:     Kevin Kappelmann
*)
functor Instantiate_QNode(
    structure N : QNODE
    type ('i, 'a, 'b, 'c, 'd) inst1
    type ('i, 'a, 'b, 'c, 'd) inst2
    type ('i, 'a, 'b, 'c, 'd) inst3
    type ('i, 'a, 'b, 'c, 'd) inst4
  ) :
    QNODE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) N.content
    where type ('i, 'a, 'b, 'c, 'd) next = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) N.next
    where type ('i, 'a, 'b, 'c, 'd) node = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) N.node
  = N

functor Replace_QNode_Content_Next(
    structure N : QNODE
    type ('i, 'a, 'b, 'c, 'd) ncontent
    val ncontent : ('i, 'a, 'b, 'c, 'd) N.content -> ('i, 'a, 'b, 'c, 'd) ncontent
    val dest_ncontent : ('i, 'a, 'b, 'c, 'd) ncontent -> ('i, 'a, 'b, 'c, 'd) N.content
    type ('i, 'a, 'b, 'c, 'd) nnext
    val nnext : ('i, 'a, 'b, 'c, 'd) N.next -> ('i, 'a, 'b, 'c, 'd) nnext
    val dest_nnext : ('i, 'a, 'b, 'c, 'd) nnext -> ('i, 'a, 'b, 'c, 'd) N.next
  ) :
    QNODE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent
    where type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) nnext
    where type ('i, 'a, 'b, 'c, 'd) node = ('i, 'a, 'b, 'c, 'd) N.node
  =
struct

type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent
type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) nnext
type ('i, 'a, 'b, 'c, 'd) node = ('i, 'a, 'b, 'c, 'd) N.node
fun node c n = N.node (dest_ncontent c) (dest_nnext n)
fun dest_node x = N.dest_node x
  |> (fn {content, next} => {content = ncontent content, next = nnext next})

fun content _ = SLens.comp_get_modify ncontent dest_ncontent (N.content ())
fun next _ = SLens.comp_get_modify nnext dest_nnext (N.next ())

fun get_content x = x |> (content () |> SLens.get)
fun get_next x = x |> (next () |> SLens.get)

fun map_content x = x |> (content () |> SLens.modify |> curry)
fun map_next x = x |> (next () |> SLens.modify  |> curry)

end
