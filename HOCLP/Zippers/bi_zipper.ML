(*  Title:      HOCLP/bi_zipper.ML
    Author:     Kevin Kappelmann
*)
signature BI_ZIPPER_MOVE =
sig
  include ZIPPER_MOVE_BASE
  type ('a, 'b) from
  type ('a, 'b) to
  val move : (('a, 'b) from, ('a, 'b) to) move
end

signature HOM_BI_ZIPPER_MOVE =
sig
  include BI_ZIPPER_MOVE
  sharing type from = to
end

functor Hom_Bi_Zipper_Move(
    structure ZM : ZIPPER_MOVE_BASE
    type ('a, 'b) data
    val move : (('a, 'b) data, ('a, 'b) data) ZM.move
  ) : HOM_BI_ZIPPER_MOVE =
struct
open ZM
type ('a, 'b) from = ('a, 'b) data
type ('a, 'b) to = ('a, 'b) data
val move = move
end

signature BI_ZIPPER_MOVES =
sig
  include ZIPPER_MOVE_BASE

  structure Init : BI_ZIPPER_MOVE
  sharing type Init.K.M.t = K.M.t
  structure Up : BI_ZIPPER_MOVE
  sharing type Up.K.M.t = K.M.t
  structure Down : BI_ZIPPER_MOVE
  sharing type Down.K.M.t = K.M.t
  structure Left : BI_ZIPPER_MOVE
  sharing type Left.K.M.t = K.M.t
  structure Right : BI_ZIPPER_MOVE
  sharing type Right.K.M.t = K.M.t
end

signature HOM_BI_ZIPPER_MOVES =
sig
  type ('a, 'b) init_from
  type ('a, 'b) data

  include BI_ZIPPER_MOVES
  sharing type Init.from = init_from
  sharing type Init.to = data
  sharing type Up.from = data
  sharing type Up.to = data
  sharing type Down.from = data
  sharing type Down.to = data
  sharing type Left.from = data
  sharing type Left.to = data
  sharing type Right.from = data
  sharing type Right.to = data
end

functor Hom_Bi_Zipper_Moves(
    structure ZM : ZIPPER_MOVE_BASE
    type ('a, 'b) init_from
    type ('a, 'b) data
    val init : (('a, 'b) init_from, ('a, 'b) data) ZM.move
    val up : (('a, 'b) data, ('a, 'b) data) ZM.move
    val down : (('a, 'b) data, ('a, 'b) data) ZM.move
    val left : (('a, 'b) data, ('a, 'b) data) ZM.move
    val right : (('a, 'b) data, ('a, 'b) data) ZM.move
  ) : HOM_BI_ZIPPER_MOVES =
struct

open ZM
type ('a, 'b) init_from = ('a, 'b) init_from
type ('a, 'b) data = ('a, 'b) data

structure Init =
struct
  open ZM
  type ('a, 'b) from = ('a, 'b) init_from
  type ('a, 'b) to = ('a, 'b) data
  val move = init
end

structure Up =
  Hom_Bi_Zipper_Move(structure ZM = ZM; type ('a, 'b) data = ('a, 'b) data; val move = up)
structure Down =
  Hom_Bi_Zipper_Move(structure ZM = ZM; type ('a, 'b) data = ('a, 'b) data; val move = down)
structure Left =
  Hom_Bi_Zipper_Move(structure ZM = ZM; type ('a, 'b) data = ('a, 'b) data; val move = left)
structure Right =
  Hom_Bi_Zipper_Move(structure ZM = ZM; type ('a, 'b) data = ('a, 'b) data; val move = right)

end

signature BI_ZIPPER_BASE =
sig
  type ('c1, 'c2) content
  type ('c1, 'c2) zcontext
  type ('c1, 'c2) zipper
  val zipper : ('c1, 'c2) content -> ('c1, 'c2) zcontext -> ('c1, 'c2) zipper

  val get_content : ('c1, 'c2) zipper -> ('c1, 'c2) content
  val get_zcontext : ('c1, 'c2) zipper -> ('c1, 'c2) zcontext

  val map_content : (('c1, 'c2) content -> ('c1, 'c2) content) -> ('c1, 'c2) zipper ->
    ('c1, 'c2) zipper
  val map_zcontext : (('c1, 'c2) zcontext -> ('c1, 'c2) zcontext) -> ('c1, 'c2) zipper ->
    ('c1, 'c2) zipper

  type ('c1, 'c2) container
  val unzip : ('c1, 'c2) zipper -> ('c1, 'c2) container
end

signature BI_ZIPPER =
sig
  include BI_ZIPPER_BASE
  include HOM_BI_ZIPPER_MOVES
  sharing type init_from = container
  sharing type data = zipper
end

functor Bi_Zipper(
    structure Z : BI_ZIPPER_BASE
    structure ZM : ZIPPER_MOVE_BASE
    val init : (('a, 'b) Z.container, ('a, 'b) Z.zipper) ZM.move
    val up : (('a, 'b) Z.zipper, ('a, 'b) Z.zipper) ZM.move
    val down : (('a, 'b) Z.zipper, ('a, 'b) Z.zipper) ZM.move
    val left : (('a, 'b) Z.zipper, ('a, 'b) Z.zipper) ZM.move
    val right : (('a, 'b) Z.zipper, ('a, 'b) Z.zipper) ZM.move
  ) : BI_ZIPPER =
struct

open Z

structure ZM = Hom_Bi_Zipper_Moves(
  structure ZM = ZM
  type ('a, 'b) init_from = ('a, 'b) container
  type ('a, 'b) data = ('a, 'b) zipper
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
)
open ZM

end