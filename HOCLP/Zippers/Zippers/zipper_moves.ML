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

signature QZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS =
sig
  include MOVE_BASE
  type ('i, 'a, 'b, 'c, 'd) init_content
  type ('i, 'a, 'b, 'c, 'd) up_content
  type ('i, 'a, 'b, 'c, 'd) down_content
  type ('i, 'a, 'b, 'c, 'd) left_content
  type ('i, 'a, 'b, 'c, 'd) right_content
end

functor QZipper_Moves_Zipper_Moves(
    structure CA : QZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS
    structure M : ZIPPER_MOVES
    sharing type CA.cat = M.cat
  ) : QZIPPER_MOVES =
struct
open CA
structure Init = QMove_Move(type ('i, 'a, 'b, 'c, 'd) content =
  ('i, 'a, 'b, 'c, 'd) init_content; structure M = M.Init)
structure Up = QMove_Move(type ('i, 'a, 'b, 'c, 'd) content =
  ('i, 'a, 'b, 'c, 'd) up_content; structure M = M.Up)
structure Down = QMove_Move(type ('i, 'a, 'b, 'c, 'd) content =
  ('i, 'a, 'b, 'c, 'd) down_content; structure M = M.Down)
structure Left = QMove_Move(type ('i, 'a, 'b, 'c, 'd) content =
  ('i, 'a, 'b, 'c, 'd) left_content; structure M = M.Left)
structure Right = QMove_Move(type ('i, 'a, 'b, 'c, 'd) content =
  ('i, 'a, 'b, 'c, 'd) right_content; structure M = M.Right)
end

functor Zipper_Moves_QZipper_Moves(M : QZIPPER_MOVES) : ZIPPER_MOVES =
struct
structure ZM = M
structure M : MOVE_BASE =ZM
open M

structure Init = Move_QMove(ZM.Init)
structure Up = Move_QMove(ZM.Up)
structure Down = Move_QMove(ZM.Down)
structure Left = Move_QMove(ZM.Left)
structure Right = Move_QMove(ZM.Right)
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

functor Hom_QZipper_Moves_Hom_Zipper_Moves(
    type ('i, 'a, 'b, 'c, 'd) content
    structure M : HOM_ZIPPER_MOVES
  ) : HOM_QZIPPER_MOVES =
struct
structure ZM = QZipper_Moves_Zipper_Moves(
  structure CA  =
  struct
    structure M : MOVE_BASE = M
    open M
    type ('i, 'a, 'b, 'c, 'd) init_content = ('i, 'a, 'b, 'c, 'd) content
    type ('i, 'a, 'b, 'c, 'd) up_content = ('i, 'a, 'b, 'c, 'd) content
    type ('i, 'a, 'b, 'c, 'd) down_content = ('i, 'a, 'b, 'c, 'd) content
    type ('i, 'a, 'b, 'c, 'd) left_content = ('i, 'a, 'b, 'c, 'd) content
    type ('i, 'a, 'b, 'c, 'd) right_content = ('i, 'a, 'b, 'c, 'd) content
  end
  structure M = M)
open ZM
type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a, 'b, 'c, 'd) Init.from
type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) Init.to
end

functor Hom_Zipper_Moves_Hom_QZipper_Moves(M : HOM_QZIPPER_MOVES) : HOM_ZIPPER_MOVES =
struct
structure ZM = Zipper_Moves_QZipper_Moves(M)
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
Hom_Zipper_Moves_Hom_QZipper_Moves(Hom_QZipper_Moves(
  structure M = M
  type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a) init_from
  type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a) data
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
))
