(*  Title:      HOCLP/bi_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature BI_ZIPPER_MOVES =
sig
  include MOVE_BASE

  structure Init : BI_MOVE
  sharing type Init.cat = cat
  structure Up : BI_MOVE
  sharing type Up.cat = cat
  structure Down : BI_MOVE
  sharing type Down.cat = cat
  structure Left : BI_MOVE
  sharing type Left.cat = cat
  structure Right : BI_MOVE
  sharing type Right.cat = cat
end

signature HOM_BI_ZIPPER_MOVES =
sig
  type ('i, 'a, 'b) init_from
  type ('i, 'a, 'b) data

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
    structure M : MOVE_BASE
    type ('i, 'a, 'b) init_from
    type ('i, 'a, 'b) data
    val init : ('i, ('i, 'a, 'b) init_from, ('i, 'a, 'b) data) M.move
    val up : ('i, ('i, 'a, 'b) data) M.hom_move
    val down : ('i, ('i, 'a, 'b) data) M.hom_move
    val left : ('i, ('i, 'a, 'b) data) M.hom_move
    val right : ('i, ('i, 'a, 'b) data) M.hom_move
  ) : HOM_BI_ZIPPER_MOVES =
struct

open M
type ('i, 'a, 'b) init_from = ('i, 'a, 'b) init_from
type ('i, 'a, 'b) data = ('i, 'a, 'b) data

structure Init =
struct
  open M
  type ('i, 'a, 'b) from = ('i, 'a, 'b) init_from
  type ('i, 'a, 'b) to = ('i, 'a, 'b) data
  val move = init
end

structure Base = struct structure M = M; type ('i, 'a, 'b) data = ('i, 'a, 'b) data end

structure Up = Hom_Bi_Move(open Base; val move = up)
structure Down = Hom_Bi_Move(open Base; val move = down)
structure Left = Hom_Bi_Move(open Base; val move = left)
structure Right = Hom_Bi_Move(open Base; val move = right)

end

functor Instantiate_Bi_Zipper_Moves(
    type ('i, 'a, 'b) inst1
    type ('i, 'a, 'b) inst2
    structure M : BI_ZIPPER_MOVES
  ) :
    BI_ZIPPER_MOVES
    where type ('i, 'a, 'b) Init.from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Init.from
    where type ('i, 'a, 'b) Init.to = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Init.to
    where type ('i, 'a, 'b) Up.from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Up.from
    where type ('i, 'a, 'b) Up.to = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Up.to
    where type ('i, 'a, 'b) Down.from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Down.from
    where type ('i, 'a, 'b) Down.to = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Down.to
    where type ('i, 'a, 'b) Left.from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Left.from
    where type ('i, 'a, 'b) Left.to = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Left.to
    where type ('i, 'a, 'b) Right.from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Right.from
    where type ('i, 'a, 'b) Right.to = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.Right.to
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.Init.cat
  = M

functor Instantiate_Hom_Bi_Zipper_Moves(
    type ('i, 'a, 'b) inst1
    type ('i, 'a, 'b) inst2
    structure M : HOM_BI_ZIPPER_MOVES
  ) :
    HOM_BI_ZIPPER_MOVES
    where type ('i, 'a, 'b) init_from = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.init_from
    where type ('i, 'a, 'b) data = ('i, ('i, 'a, 'b) inst1, ('i, 'a, 'b) inst2) M.data
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.Init.cat
  = M

