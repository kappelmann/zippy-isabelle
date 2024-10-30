(*  Title:      HOCLP/pair_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ZIPPER_MOVES =
sig
  structure M1 : ZIPPER_MOVES
  structure M2 : ZIPPER_MOVES

  include ZIPPER_MOVES
  where type ('i, 'a) Init.from = ('i, 'a) M1.Init.from * ('i, 'a) M2.Init.from
  where type ('i, 'a) Init.to = ('i, 'a) M1.Init.to * ('i, 'a) M2.Init.to
  where type ('i, 'a) Up.from = ('i, 'a) M1.Up.from * ('i, 'a) M2.Up.from
  where type ('i, 'a) Up.to = ('i, 'a) M1.Up.to * ('i, 'a) M2.Up.to
  where type ('i, 'a) Down.from = ('i, 'a) M1.Down.from * ('i, 'a) M2.Down.from
  where type ('i, 'a) Down.to = ('i, 'a) M1.Down.to * ('i, 'a) M2.Down.to
  where type ('i, 'a) Left.from = ('i, 'a) M1.Left.from * ('i, 'a) M2.Left.from
  where type ('i, 'a) Left.to = ('i, 'a) M1.Left.to * ('i, 'a) M2.Left.to
  where type ('i, 'a) Right.from = ('i, 'a) M1.Right.from * ('i, 'a) M2.Right.from
  where type ('i, 'a) Right.to = ('i, 'a) M1.Right.to * ('i, 'a) M2.Right.to
  sharing type M1.cat = cat
  sharing type M2.cat = cat
end

functor Pair_QZipper_Moves_Pair_Zipper_Moves(
    structure CA : QZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS
    structure PM : PAIR_ZIPPER_MOVES
    sharing type CA.cat = PM.cat
  ) : PAIR_QZIPPER_MOVES =
struct
structure Base = struct structure CA = CA end
structure M1 = QZipper_Moves_Zipper_Moves(open Base; structure M = PM.M1)
structure M2 = QZipper_Moves_Zipper_Moves(open Base; structure M = PM.M2)
structure M = QZipper_Moves_Zipper_Moves(open Base; structure M = PM)
open M
end

functor Pair_Zipper_Moves_Pair_QZipper_Moves(PM : PAIR_QZIPPER_MOVES) : PAIR_ZIPPER_MOVES =
struct
structure M1 = Zipper_Moves_QZipper_Moves(PM.M1)
structure M2 = Zipper_Moves_QZipper_Moves(PM.M2)
structure M = Zipper_Moves_QZipper_Moves(PM)
open M
end

functor Pair_Zipper_Moves(
    structure A : LAZY_IARROW_BASE
    structure M1 : ZIPPER_MOVES
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.cat
    structure M2 : ZIPPER_MOVES
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M1.cat
  ) : PAIR_ZIPPER_MOVES =
struct

structure CA =
struct
  structure M : MOVE_BASE = M1
  open M
  type ('i, 'a, 'b, 'c, 'd) init_content = 'a
  type ('i, 'a, 'b, 'c, 'd) up_content = 'a
  type ('i, 'a, 'b, 'c, 'd) down_content = 'a
  type ('i, 'a, 'b, 'c, 'd) left_content = 'a
  type ('i, 'a, 'b, 'c, 'd) right_content = 'a
end

structure PM = Pair_Zipper_Moves_Pair_QZipper_Moves(Pair_QZipper_Moves(
  structure A = A
  structure Base = struct structure CA = CA end
  structure M1 = QZipper_Moves_Zipper_Moves(open Base; structure M = M1)
  structure M2 = QZipper_Moves_Zipper_Moves(open Base; structure M = M2))
)
open PM

end
