(*  Title:      HOCLP/replace_zipper4_moves_zipper.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper4_Moves_Zipper(
    structure C : LAZY_SEMI_CATEGORY_BASE
    structure Z : ZIPPER4_MOVES
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) C.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    val nzipper : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper) Z.move
    val dest_nzipper : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper, ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper) Z.move
  )
  : ZIPPER4_MOVES
    where type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) Z.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) Z.cat
  =
Zipper4_Moves(
  structure M = Z
  open Z
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
  structure Base = struct
    structure C = C
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    val dest_nfrom = dest_nzipper
    val nto = nzipper
  end
  structure Zip = Replace_Move4_To(open Base; structure M = Z.Zip)
  val zip = Zip.move
  structure Unzip = Replace_Move4_From(open Base; structure M = Z.Unzip)
  val unzip = Unzip.move
  structure Up = Replace_Move4_From_To(open Base; structure M = Z.Up)
  val up = Up.move
  structure Down = Replace_Move4_From_To(open Base; structure M = Z.Down)
  val down = Down.move
  structure Left = Replace_Move4_From_To(open Base; structure M = Z.Left)
  val left = Left.move
  structure Right = Replace_Move4_From_To(open Base; structure M = Z.Right)
  val right = Right.move
)