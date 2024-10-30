(*  Title:      HOCLP/qzipper.ML
    Author:     Kevin Kappelmann
*)
signature QZIPPER_BASE =
sig
  type ('i, 'a, 'b, 'c, 'd) content
  type ('i, 'a, 'b, 'c, 'd) zcontext
  type ('i, 'a, 'b, 'c, 'd) zipper
  val zipper : ('i, 'a, 'b, 'c, 'd) content -> ('i, 'a, 'b, 'c, 'd) zcontext ->
    ('i, 'a, 'b, 'c, 'd) zipper

  val get_content : ('i, 'a, 'b, 'c, 'd) zipper -> ('i, 'a, 'b, 'c, 'd) content
  val get_zcontext : ('i, 'a, 'b, 'c, 'd) zipper -> ('i, 'a, 'b, 'c, 'd) zcontext

  val map_content : (('i, 'a, 'b, 'c, 'd) content -> ('i, 'a, 'b, 'c, 'd) content) ->
    ('i, 'a, 'b, 'c, 'd) zipper -> ('i, 'a, 'b, 'c, 'd) zipper
  val map_zcontext : (('i, 'a, 'b, 'c, 'd) zcontext -> ('i, 'a, 'b, 'c, 'd) zcontext) ->
    ('i, 'a, 'b, 'c, 'd) zipper -> ('i, 'a, 'b, 'c, 'd) zipper

  type ('i, 'a, 'b, 'c, 'd) container
  val unzip : ('i, 'a, 'b, 'c, 'd) zipper -> ('i, 'a, 'b, 'c, 'd) container
end

signature QZIPPER =
sig
  include QZIPPER_BASE
  val content : unit -> (('i, 'a, 'b, 'c, 'd) zipper, ('i, 'a, 'b, 'c, 'd) content,
    ('i, 'a, 'b, 'c, 'd) zipper, ('i, 'a, 'b, 'c, 'd) content) SLens.lens
  val zcontext : unit -> (('i, 'a, 'b, 'c, 'd) zipper, ('i, 'a, 'b, 'c, 'd) zcontext,
    ('i, 'a, 'b, 'c, 'd) zipper, ('i, 'a, 'b, 'c, 'd) zcontext) SLens.lens
  include HOM_QZIPPER_MOVES
  sharing type init_from = container
  sharing type data = zipper
end

functor QZipper(
    structure Z : QZIPPER_BASE
    structure M : MOVE_BASE
    val init : ('i, ('i, 'a, 'b, 'c, 'd) Z.container, ('i, 'a, 'b, 'c, 'd) Z.zipper) M.move
    val up : ('i, ('i, 'a, 'b, 'c, 'd) Z.zipper) M.hom_move
    val down : ('i, ('i, 'a, 'b, 'c, 'd) Z.zipper) M.hom_move
    val left : ('i, ('i, 'a, 'b, 'c, 'd) Z.zipper) M.hom_move
    val right : ('i, ('i, 'a, 'b, 'c, 'd) Z.zipper) M.hom_move
  ) : QZIPPER =
struct

open Z

fun content _ = SLens.lens get_content (uncurry map_content)
fun zcontext _ = SLens.lens get_zcontext (uncurry map_zcontext)

structure ZMS = Hom_QZipper_Moves(
  structure M = M
  type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a, 'b, 'c, 'd) container
  type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) zipper
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
)
open ZMS

end

functor QZipper_QZipper_Moves(
    structure Z : QZIPPER_BASE
    structure M : HOM_QZIPPER_MOVES
    sharing type M.init_from = Z.container
    sharing type M.data = Z.zipper
  ) : QZIPPER =
QZipper(
  structure Z = Z
  structure M = M
  val init = M.Init.move
  val up = M.Up.move
  val down = M.Down.move
  val left = M.Left.move
  val right = M.Right.move
)

functor Instantiate_QZipper_Base(
    type ('i, 'a, 'b, 'c, 'd) inst1
    type ('i, 'a, 'b, 'c, 'd) inst2
    type ('i, 'a, 'b, 'c, 'd) inst3
    type ('i, 'a, 'b, 'c, 'd) inst4
    structure Z : QZIPPER_BASE
  ) :
    QZIPPER_BASE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.content
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.zipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.container
  = Z

functor Instantiate_QZipper(
    type ('i, 'a, 'b, 'c, 'd) inst1
    type ('i, 'a, 'b, 'c, 'd) inst2
    type ('i, 'a, 'b, 'c, 'd) inst3
    type ('i, 'a, 'b, 'c, 'd) inst4
    structure Z : QZIPPER
  ) :
    QZIPPER
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.content
    where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.zcontext
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.zipper
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) Z.container
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) Z.Init.cat
  = Z
