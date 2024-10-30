(*  Title:      HOCLP/qzipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature QZIPPER_MOVES =
sig
  include MOVE_BASE

  structure Init : QMOVE
  sharing type Init.cat = cat
  structure Up : QMOVE
  sharing type Up.cat = cat
  structure Down : QMOVE
  sharing type Down.cat = cat
  structure Left : QMOVE
  sharing type Left.cat = cat
  structure Right : QMOVE
  sharing type Right.cat = cat
end

signature HOM_QZIPPER_MOVES =
sig
  type ('i, 'a, 'b, 'c, 'd) init_from
  type ('i, 'a, 'b, 'c, 'd) data

  include QZIPPER_MOVES
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

functor Hom_QZipper_Moves(
    structure M : MOVE_BASE
    type ('i, 'a, 'b, 'c, 'd) init_from
    type ('i, 'a, 'b, 'c, 'd) data
    val init : ('i, ('i, 'a, 'b, 'c, 'd) init_from, ('i, 'a, 'b, 'c, 'd) data) M.move
    val up : ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
    val down : ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
    val left : ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
    val right : ('i, ('i, 'a, 'b, 'c, 'd) data) M.hom_move
  ) : HOM_QZIPPER_MOVES =
struct

open M
type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a, 'b, 'c, 'd) init_from
type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) data

structure Init =
struct
  open M
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) init_from
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) data
  val move = init
end

structure Base = struct structure M = M; type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) data end

structure Up = Hom_QMove(open Base; val move = up)
structure Down = Hom_QMove(open Base; val move = down)
structure Left = Hom_QMove(open Base; val move = left)
structure Right = Hom_QMove(open Base; val move = right)

end

functor Instantiate_QZipper_Moves(
    type ('i, 'a, 'b, 'c, 'd) inst1
    type ('i, 'a, 'b, 'c, 'd) inst2
    type ('i, 'a, 'b, 'c, 'd) inst3
    type ('i, 'a, 'b, 'c, 'd) inst4
    structure M : QZIPPER_MOVES
  ) :
    QZIPPER_MOVES
    where type ('i, 'a, 'b, 'c, 'd) Init.from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Init.from
    where type ('i, 'a, 'b, 'c, 'd) Init.to = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Init.to
    where type ('i, 'a, 'b, 'c, 'd) Up.from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Up.from
    where type ('i, 'a, 'b, 'c, 'd) Up.to = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Up.to
    where type ('i, 'a, 'b, 'c, 'd) Down.from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Down.from
    where type ('i, 'a, 'b, 'c, 'd) Down.to = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Down.to
    where type ('i, 'a, 'b, 'c, 'd) Left.from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Left.from
    where type ('i, 'a, 'b, 'c, 'd) Left.to = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Left.to
    where type ('i, 'a, 'b, 'c, 'd) Right.from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Right.from
    where type ('i, 'a, 'b, 'c, 'd) Right.to = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.Right.to
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.Init.cat
  = M

functor Instantiate_Hom_QZipper_Moves(
    type ('i, 'a, 'b, 'c, 'd) inst1
    type ('i, 'a, 'b, 'c, 'd) inst2
    type ('i, 'a, 'b, 'c, 'd) inst3
    type ('i, 'a, 'b, 'c, 'd) inst4
    structure M : HOM_QZIPPER_MOVES
  ) :
    HOM_QZIPPER_MOVES
    where type ('i, 'a, 'b, 'c, 'd) init_from = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.init_from
    where type ('i, 'a, 'b, 'c, 'd) data = ('i, ('i, 'a, 'b, 'c, 'd) inst1,
      ('i, 'a, 'b, 'c, 'd) inst2, ('i, 'a, 'b, 'c, 'd) inst3, ('i, 'a, 'b, 'c, 'd) inst4) M.data
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  = M

functor Replace_Hom_QZipper_Moves_Data(
    structure C : LAZY_ISEMI_CATEGORY_BASE
    structure M : HOM_QZIPPER_MOVES
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) C.T.lcat
    type ('i, 'a, 'b, 'c, 'd) ndata
    val ndata : ('i, ('i, 'a, 'b, 'c, 'd) M.data, ('i, 'a, 'b, 'c, 'd) ndata) M.move
    val dest_ndata : ('i, ('i, 'a, 'b, 'c, 'd) ndata, ('i, 'a, 'b, 'c, 'd) M.data) M.move
  )
  : HOM_QZIPPER_MOVES
    where type ('i, 'a, 'b, 'c, 'd) init_from = ('i, 'a, 'b, 'c, 'd) M.init_from
    where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) ndata
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  =
Hom_QZipper_Moves(
  structure M = M
  open M
  type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) ndata
  structure Base = struct
    structure C = C
    type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) ndata
    type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'a, 'b, 'c, 'd) ndata
    val dest_nfrom = dest_ndata
    val nto = ndata
  end
  structure Init = Replace_QMove_To(open Base; structure M = M.Init)
  val init = Init.move
  structure Up = Replace_QMove_From_To(open Base; structure M = M.Up)
  val up = Up.move
  structure Down = Replace_QMove_From_To(open Base; structure M = M.Down)
  val down = Down.move
  structure Left = Replace_QMove_From_To(open Base; structure M = M.Left)
  val left = Left.move
  structure Right = Replace_QMove_From_To(open Base; structure M = M.Right)
  val right = Right.move
)