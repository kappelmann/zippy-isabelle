(*  Title:      HOCLP/bi_zipper.ML
    Author:     Kevin Kappelmann
*)
signature BI_ZIPPER_BASE =
sig
  type ('i, 'a, 'b) content
  type ('i, 'a, 'b) zcontext
  type ('i, 'a, 'b) zipper
  val zipper : ('i, 'a, 'b) content -> ('i, 'a, 'b) zcontext -> ('i, 'a, 'b) zipper

  val get_content : ('i, 'a, 'b) zipper -> ('i, 'a, 'b) content
  val get_zcontext : ('i, 'a, 'b) zipper -> ('i, 'a, 'b) zcontext

  val map_content : (('i, 'a, 'b) content -> ('i, 'a, 'b) content) -> ('i, 'a, 'b) zipper ->
    ('i, 'a, 'b) zipper
  val map_zcontext : (('i, 'a, 'b) zcontext -> ('i, 'a, 'b) zcontext) -> ('i, 'a, 'b) zipper ->
    ('i, 'a, 'b) zipper

  type ('i, 'a, 'b) container
  val unzip : ('i, 'a, 'b) zipper -> ('i, 'a, 'b) container
end

signature BI_ZIPPER =
sig
  include BI_ZIPPER_BASE
  val content : unit ->
    (('i, 'a, 'b) zipper, ('i, 'a, 'b) content, ('i, 'a, 'b) zipper, ('i, 'a, 'b) content) SLens.lens
  val zcontext : unit ->
    (('i, 'a, 'b) zipper, ('i, 'a, 'b) zcontext, ('i, 'a, 'b) zipper, ('i, 'a, 'b) zcontext) SLens.lens
  include HOM_BI_ZIPPER_MOVES
  sharing type init_from = container
  sharing type data = zipper
end

functor Bi_Zipper(
    structure Z : BI_ZIPPER_BASE
    structure M : MOVE_BASE
    val init : ('i, ('i, 'a, 'b) Z.container, ('i, 'a, 'b) Z.zipper) M.move
    val up : ('i, ('i, 'a, 'b) Z.zipper) M.hom_move
    val down : ('i, ('i, 'a, 'b) Z.zipper) M.hom_move
    val left : ('i, ('i, 'a, 'b) Z.zipper) M.hom_move
    val right : ('i, ('i, 'a, 'b) Z.zipper) M.hom_move
  ) : BI_ZIPPER =
struct

open Z

fun content _ = SLens.lens get_content (uncurry map_content)
fun zcontext _ = SLens.lens get_zcontext (uncurry map_zcontext)

structure ZMS = Hom_Bi_Zipper_Moves(
  structure M = M
  type ('i, 'a, 'b) init_from = ('i, 'a, 'b) container
  type ('i, 'a, 'b) data = ('i, 'a, 'b) zipper
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
)
open ZMS

end

functor Bi_Zipper_Bi_Zipper_Moves(
    structure Z : BI_ZIPPER_BASE
    structure M : HOM_BI_ZIPPER_MOVES
    sharing type M.init_from = Z.container
    sharing type M.data = Z.zipper
  ) : BI_ZIPPER =
Bi_Zipper(
  structure Z = Z
  structure M = M
  val init = M.Init.move
  val up = M.Up.move
  val down = M.Down.move
  val left = M.Left.move
  val right = M.Right.move
)

functor Instantiate_Bi_Zipper_Base(
    type ('i, 'a, 'b) inst1
    type ('i, 'a, 'b) inst2
    structure Z : BI_ZIPPER_BASE
  ) :
    BI_ZIPPER_BASE
    where type ('i, 'a, 'b) content = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.content
    where type ('i, 'a, 'b) zcontext = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.zcontext
    where type ('i, 'a, 'b) zipper = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.zipper
    where type ('i, 'a, 'b) container = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.container
  = Z

functor Instantiate_Bi_Zipper(
    type ('i, 'a, 'b) inst1
    type ('i, 'a, 'b) inst2
    structure Z : BI_ZIPPER
  ) :
    BI_ZIPPER
    where type ('i, 'a, 'b) content = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.content
    where type ('i, 'a, 'b) zcontext = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.zcontext
    where type ('i, 'a, 'b) zipper = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.zipper
    where type ('i, 'a, 'b) container = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) Z.container
    where type ('i, 'j, 'a, 'b) C.cat = ('i, 'j, 'a, 'b) Z.Init.C.cat
  = Z
