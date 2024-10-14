(*  Title:      HOCLP/zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_MOVES =
sig
  include MOVE_BASE

  structure Init : MOVE
  sharing type Init.cat = cat
  structure Up : MOVE
  sharing type Up.cat = cat
  structure Down : MOVE
  sharing type Down.cat = cat
  structure Left : MOVE
  sharing type Left.cat = cat
  structure Right : MOVE
  sharing type Right.cat = cat
end

signature BI_ZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS =
sig
  include MOVE_BASE
  type ('i, 'a, 'b) init_content
  type ('i, 'a, 'b) up_content
  type ('i, 'a, 'b) down_content
  type ('i, 'a, 'b) left_content
  type ('i, 'a, 'b) right_content
end

functor Bi_Zipper_Moves_Zipper_Moves(
    structure CA : BI_ZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS
    structure M : ZIPPER_MOVES
    sharing type CA.cat = M.cat
  ) : BI_ZIPPER_MOVES =
struct
open CA
structure Init = Bi_Move_Move(type ('i, 'a, 'b) content = ('i, 'a, 'b) init_content; structure M = M.Init)
structure Up = Bi_Move_Move(type ('i, 'a, 'b) content = ('i, 'a, 'b) up_content; structure M = M.Up)
structure Down = Bi_Move_Move(type ('i, 'a, 'b) content = ('i, 'a, 'b) down_content; structure M = M.Down)
structure Left = Bi_Move_Move(type ('i, 'a, 'b) content = ('i, 'a, 'b) left_content; structure M = M.Left)
structure Right = Bi_Move_Move(type ('i, 'a, 'b) content = ('i, 'a, 'b) right_content; structure M = M.Right)
end

functor Zipper_Moves_Bi_Zipper_Moves(M : BI_ZIPPER_MOVES) : ZIPPER_MOVES =
struct
structure ZM = M
structure M : MOVE_BASE =ZM
open M

structure Init = Move_Bi_Move(ZM.Init)
structure Up = Move_Bi_Move(ZM.Up)
structure Down = Move_Bi_Move(ZM.Down)
structure Left = Move_Bi_Move(ZM.Left)
structure Right = Move_Bi_Move(ZM.Right)
end

signature HOM_ZIPPER_MOVES =
sig
  type ('i, 'a) init_from
  type ('i, 'a) data

  include ZIPPER_MOVES
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

functor Hom_Bi_Zipper_Moves_Hom_Zipper_Moves(
    type ('i, 'a, 'b) content
    structure M : HOM_ZIPPER_MOVES
  ) : HOM_BI_ZIPPER_MOVES =
struct
structure ZM = Bi_Zipper_Moves_Zipper_Moves(
  structure CA  =
  struct
    structure M : MOVE_BASE = M
    open M
    type ('i, 'a, 'b) init_content = ('i, 'a, 'b) content
    type ('i, 'a, 'b) up_content = ('i, 'a, 'b) content
    type ('i, 'a, 'b) down_content = ('i, 'a, 'b) content
    type ('i, 'a, 'b) left_content = ('i, 'a, 'b) content
    type ('i, 'a, 'b) right_content = ('i, 'a, 'b) content
  end
  structure M = M)
open ZM
type ('i, 'a, 'b) init_from = ('i, 'a, 'b) Init.from
type ('i, 'a, 'b) data = ('i, 'a, 'b) Init.to
end

functor Hom_Zipper_Moves_Hom_Bi_Zipper_Moves(M : HOM_BI_ZIPPER_MOVES) : HOM_ZIPPER_MOVES =
struct
structure ZM = Zipper_Moves_Bi_Zipper_Moves(M)
open ZM
type ('i, 'a) init_from = ('i, 'a) Init.from
type ('i, 'a) data = ('i, 'a) Init.to
end

functor Hom_Zipper_Moves(
    structure M : MOVE_BASE
    type ('i, 'a) init_from
    type ('i, 'a) data
    val init : ('i, ('i, 'a) init_from, ('i, 'a) data) M.move
    val up : ('i, ('i, 'a) data) M.hom_move
    val down : ('i, ('i, 'a) data) M.hom_move
    val left : ('i, ('i, 'a) data) M.hom_move
    val right : ('i, ('i, 'a) data) M.hom_move
  ) : HOM_ZIPPER_MOVES =
Hom_Zipper_Moves_Hom_Bi_Zipper_Moves(Hom_Bi_Zipper_Moves(
  structure M = M
  type ('i, 'a, 'b) init_from = ('i, 'a) init_from
  type ('i, 'a, 'b) data = ('i, 'a) data
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
))
