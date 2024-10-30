(*  Title:      HOCLP/replace_qzipper_content.ML
    Author:     Kevin Kappelmann
*)
functor Replace_QZipper_Base_Content(
    structure Z : QZIPPER_BASE
    type ('i, 'a, 'b, 'c, 'd) ncontent
    val ncontent : ('i, 'a, 'b, 'c, 'd) Z.content -> ('i, 'a, 'b, 'c, 'd) ncontent
    val dest_ncontent : ('i, 'a, 'b, 'c, 'd) ncontent -> ('i, 'a, 'b, 'c, 'd) Z.content
  ) :
    QZIPPER_BASE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) Z.zipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z.container
  =
struct

open Z
type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent

fun zipper x = x |> dest_ncontent |> Z.zipper
fun get_content x = x |> Z.get_content |> ncontent
fun map_content f = Z.map_content (ncontent #> f #> dest_ncontent)

end

functor Replace_QZipper_Content(
    structure Z : QZIPPER
    type ('i, 'a, 'b, 'c, 'd) ncontent
    val ncontent : ('i, 'a, 'b, 'c, 'd) Z.content -> ('i, 'a, 'b, 'c, 'd) ncontent
    val dest_ncontent : ('i, 'a, 'b, 'c, 'd) ncontent -> ('i, 'a, 'b, 'c, 'd) Z.content
  ) :
    QZIPPER
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) Z.zipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z.container
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) Z.cat
  =
QZipper_QZipper_Moves(
  structure M = Z
  structure Z = Replace_QZipper_Base_Content(
    structure Z = Z; type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) ncontent;
    val ncontent = ncontent; val dest_ncontent = dest_ncontent)
)
