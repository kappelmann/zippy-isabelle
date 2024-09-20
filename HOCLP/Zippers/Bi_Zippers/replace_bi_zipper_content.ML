(*  Title:      HOCLP/replace_bi_zipper_content.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Bi_Zipper_Base_Content(
    structure Z : BI_ZIPPER_BASE
    type ('i, 'a, 'b) ncontent
    val ncontent : ('i, 'a, 'b) Z.content -> ('i, 'a, 'b) ncontent
    val dest_ncontent : ('i, 'a, 'b) ncontent -> ('i, 'a, 'b) Z.content
  ) :
    BI_ZIPPER_BASE
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent
    where type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) Z.zcontext
    where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) Z.zipper
    where type ('i, 'a, 'b) container = ('i, 'a, 'b) Z.container
  =
struct

open Z
type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent

fun zipper x = x |> dest_ncontent |> Z.zipper
fun get_content x = x |> Z.get_content |> ncontent
fun map_content f = Z.map_content (ncontent #> f #> dest_ncontent)

end

functor Replace_Bi_Zipper_Content(
    structure Z : BI_ZIPPER
    type ('i, 'a, 'b) ncontent
    val ncontent : ('i, 'a, 'b) Z.content -> ('i, 'a, 'b) ncontent
    val dest_ncontent : ('i, 'a, 'b) ncontent -> ('i, 'a, 'b) Z.content
  ) :
    BI_ZIPPER
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) ncontent
    where type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) Z.zcontext
    where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) Z.zipper
    where type ('i, 'a, 'b) container = ('i, 'a, 'b) Z.container
    where type ('i, 'j, 'a, 'b) T.cat = ('i, 'j, 'a, 'b) Z.T.cat
  =
Bi_Zipper_Bi_Zipper_Moves(
  structure M = Z
  structure Z = Replace_Bi_Zipper_Base_Content(
    structure Z = Z; type ('i, 'a, 'b) ncontent = ('i, 'a, 'b) ncontent;
    val ncontent = ncontent; val dest_ncontent = dest_ncontent)
)

functor Replace_Bi_Zipper_Container(
    structure Z : BI_ZIPPER
    type ('i, 'a, 'b) ncontainer
    val ncontainer : ('i, 'a, 'b) Z.container -> ('i, 'a, 'b) ncontainer
    val dest_ncontainer : ('i, ('i, 'a, 'b) ncontainer, ('i, 'a, 'b) Z.container) Z.move
  ) =
Bi_Zipper(
  structure M = Z
  structure Z =
  struct
    open Z
    type ('i, 'a, 'b) container = ('i, 'a, 'b) ncontainer
    fun unzip x = x |> Z.unzip |> ncontainer
  end
  fun init _ = M.comp Z.Init.move dest_ncontainer ()
  val up = Z.Up.move
  val down = Z.Down.move
  val left = Z.Left.move
  val right = Z.Right.move
)
