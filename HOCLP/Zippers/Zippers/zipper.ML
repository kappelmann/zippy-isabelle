(*  Title:      HOCLP/zipper.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_BASE =
sig
  type ('i, 'a) content
  type ('i, 'a) zcontext
  type ('i, 'a) zipper
  val zipper : ('i, 'a) content -> ('i, 'a) zcontext -> ('i, 'a) zipper

  val get_content : ('i, 'a) zipper -> ('i, 'a) content
  val get_zcontext : ('i, 'a) zipper -> ('i, 'a) zcontext

  val map_content : (('i, 'a) content -> ('i, 'a) content) -> ('i, 'a) zipper -> ('i, 'a) zipper
  val map_zcontext : (('i, 'a) zcontext -> ('i, 'a) zcontext) -> ('i, 'a) zipper -> ('i, 'a) zipper

  type ('i, 'a) container
  val unzip : ('i, 'a) zipper -> ('i, 'a) container
end

functor QZipper_Base_Zipper_Base(type ('i, 'a, 'b, 'c, 'd) content; structure Z : ZIPPER_BASE)
  : QZIPPER_BASE =
struct
type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, ('i, 'a, 'b, 'c, 'd) content) Z.zcontext
type ('i, 'a, 'b, 'c, 'd) zipper = ('i, ('i, 'a, 'b, 'c, 'd) content) Z.zipper
type ('i, 'a, 'b, 'c, 'd) container = ('i, ('i, 'a, 'b, 'c, 'd) content) Z.container
type ('i, 'a, 'b, 'c, 'd) content = ('i, ('i, 'a, 'b, 'c, 'd) content) Z.content
val zipper = Z.zipper
val get_content = Z.get_content
val get_zcontext = Z.get_zcontext
val map_content = Z.map_content
val map_zcontext = Z.map_zcontext
val unzip = Z.unzip
end

functor Zipper_Base_QZipper_Base(Z : QZIPPER_BASE) : ZIPPER_BASE =
struct
type ('i, 'a) zcontext = ('i, 'a, unit, unit, unit) Z.zcontext
type ('i, 'a) zipper = ('i, 'a, unit, unit, unit) Z.zipper
type ('i, 'a) container = ('i, 'a, unit, unit, unit) Z.container
type ('i, 'a) content = ('i, 'a, unit, unit, unit) Z.content
val zipper = Z.zipper
val get_content = Z.get_content
val get_zcontext = Z.get_zcontext
val map_content = Z.map_content
val map_zcontext = Z.map_zcontext
val unzip = Z.unzip
end

signature ZIPPER =
sig
  include ZIPPER_BASE
  val content : unit -> (('i, 'a) zipper, ('i, 'a) content, ('i, 'a) zipper, ('i, 'a) content) SLens.lens
  val zcontext : unit -> (('i, 'a) zipper, ('i, 'a) zcontext, ('i, 'a) zipper, ('i, 'a) zcontext) SLens.lens
  include HOM_ZIPPER_MOVES
  sharing type init_from = container
  sharing type data = zipper
end

functor QZipper_Zipper(type ('i, 'a, 'b, 'c, 'd) content; structure Z : ZIPPER) : QZIPPER =
struct
structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content end
structure ZB = QZipper_Base_Zipper_Base(open Base; structure Z = Z)
structure ZM = Hom_QZipper_Moves_Hom_Zipper_Moves(open Base; structure M = Z)
open ZB
open ZM
fun content _ = SLens.lens get_content (uncurry map_content)
fun zcontext _ = SLens.lens get_zcontext (uncurry map_zcontext)
end

functor Zipper_QZipper(Z : QZIPPER) : ZIPPER =
struct
structure ZB = Zipper_Base_QZipper_Base(Z)
structure ZM = Hom_Zipper_Moves_Hom_QZipper_Moves(Z)
open ZB
open ZM
fun content _ = SLens.lens get_content (uncurry map_content)
fun zcontext _ = SLens.lens get_zcontext (uncurry map_zcontext)
end

functor Zipper(
    structure Z : ZIPPER_BASE
    structure M : MOVE_BASE
    val init : ('i, ('i, 'a) Z.container, ('i, 'a) Z.zipper) M.move
    val up : ('i, ('i, 'a) Z.zipper) M.hom_move
    val down : ('i, ('i, 'a) Z.zipper) M.hom_move
    val left : ('i, ('i, 'a) Z.zipper) M.hom_move
    val right : ('i, ('i, 'a) Z.zipper) M.hom_move
  ) : ZIPPER =
Zipper_QZipper(QZipper(
  structure Z = QZipper_Base_Zipper_Base(type ('i, 'a, 'b, 'c, 'd) content = 'a; structure Z = Z)
  structure M = M
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
))

functor Zipper_Zipper_Moves(
    structure Z : ZIPPER_BASE
    structure M : HOM_ZIPPER_MOVES
    sharing type M.init_from = Z.container
    sharing type M.data = Z.zipper
  ) : ZIPPER =
Zipper_QZipper(QZipper_QZipper_Moves(
  structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = 'a end
  structure Z = QZipper_Base_Zipper_Base(open Base; structure Z = Z)
  structure M = Hom_QZipper_Moves_Hom_Zipper_Moves(open Base; structure M = M)
))