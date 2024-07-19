(*  Title:      HOCLP/modify_bi_node.ML
    Author:     Kevin Kappelmann
*)
functor Instantiate_Bi_Node(structure N : BI_NODE; type ('i, 'a, 'b) cinst; type ('i, 'a, 'b) ninst) :
    BI_NODE
    where type ('i, 'a, 'b) content = ('i, ('i, 'a, 'b) cinst, ('i, 'a, 'b) ninst) N.content
    where type ('i, 'a, 'b) next = ('i, ('i, 'a, 'b) cinst, ('i, 'a, 'b) ninst) N.next
    where type ('i, 'a, 'b) node = ('i, ('i, 'a, 'b) cinst, ('i, 'a, 'b) ninst) N.node
  = N

functor Replace_Bi_Node_Content_Next(
    structure N : BI_NODE
    type ('i, 'a, 'b) ncontent
    val ncontent : ('i, 'a, 'b) N.content -> ('i, 'a, 'b) ncontent
    val dest_ncontent : ('i, 'a, 'b) ncontent -> ('i, 'a, 'b) N.content
    type ('i, 'a, 'b) nnext
    val nnext : ('i, 'a, 'b) N.next -> ('i, 'a, 'b) nnext
    val dest_nnext : ('i, 'a, 'b) nnext -> ('i, 'a, 'b) N.next
  ) :
    BI_NODE
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent
    where type ('i, 'a, 'b) next = ('i, 'a, 'b) nnext
    where type ('i, 'a, 'b) node = ('i, 'a, 'b) N.node
  =
struct

type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent
type ('i, 'a, 'b) next = ('i, 'a, 'b) nnext
type ('i, 'a, 'b) node = ('i, 'a, 'b) N.node
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
