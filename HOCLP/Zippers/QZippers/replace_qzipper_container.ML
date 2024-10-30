(*  Title:      HOCLP/replace_qzipper_container.ML
    Author:     Kevin Kappelmann
*)
functor Replace_QZipper_Container(
    structure C : LAZY_ISEMI_CATEGORY_BASE
    structure Z : QZIPPER
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) C.T.lcat
    type ('i, 'a, 'b, 'c, 'd) ncontainer
    val ncontainer : ('i, 'a, 'b, 'c, 'd) Z.container -> ('i, 'a, 'b, 'c, 'd) ncontainer
    val dest_ncontainer : ('i, ('i, 'a, 'b, 'c, 'd) ncontainer, ('i, 'a, 'b, 'c, 'd) Z.container) Z.move
  )
  : QZIPPER
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z.content
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) Z.zipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) ncontainer
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) Z.cat
  =
QZipper(
  structure M = Z
  structure Z =
  struct
    open Z
    type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) ncontainer
    fun unzip x = x |> Z.unzip |> ncontainer
  end
  structure Init = Replace_QMove_From(
    structure C = C
    structure M = Z.Init
    type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) ncontainer
    val dest_nfrom = dest_ncontainer
  )
  val init = Init.move
  val up = Z.Up.move
  val down = Z.Down.move
  val left = Z.Left.move
  val right = Z.Right.move
)
