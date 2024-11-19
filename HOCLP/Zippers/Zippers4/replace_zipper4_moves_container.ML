(*  Title:      HOCLP/replace_zipper4_moves_container.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper4_Moves_Container(
    structure C : LAZY_SEMI_CATEGORY_BASE
    structure Z : ZIPPER4_MOVES
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) C.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer
    val ncontainer :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z.container, ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer) Z.move
    val dest_ncontainer :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer, ('p1, 'a1, 'a2, 'a3, 'a4) Z.container) Z.move
  )
  : ZIPPER4_MOVES
    where type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) Z.cat
  =
Zipper4_Moves(
  structure M = Z
  open Z
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer
  structure Base = struct
    structure C = C
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer
    type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) ncontainer
    val dest_nfrom = dest_ncontainer
    val nto = ncontainer
  end
  structure Zip = Replace_Move4_From(open Base; structure M = Z.Zip)
  val zip = Zip.move
  structure Unzip = Replace_Move4_To(open Base; structure M = Z.Unzip)
  val unzip = Unzip.move
  val up = Z.Up.move
  val down = Z.Down.move
  val left = Z.Left.move
  val right = Z.Right.move
)
