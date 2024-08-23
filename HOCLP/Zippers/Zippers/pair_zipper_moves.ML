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
  sharing type M1.C.cat = C.cat
  sharing type M2.C.cat = C.cat
end

functor Pair_Bi_Zipper_Moves_Pair_Zipper_Moves(
    structure CA : BI_ZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS
    structure PM : PAIR_ZIPPER_MOVES
    sharing type CA.C.cat = PM.C.cat
  ) : PAIR_BI_ZIPPER_MOVES =
struct
structure Base = struct structure CA = CA end
structure M1 = Bi_Zipper_Moves_Zipper_Moves(open Base; structure M = PM.M1)
structure M2 = Bi_Zipper_Moves_Zipper_Moves(open Base; structure M = PM.M2)
structure M = Bi_Zipper_Moves_Zipper_Moves(open Base; structure M = PM)
open M
end

functor Pair_Zipper_Moves_Pair_Bi_Zipper_Moves(PM : PAIR_BI_ZIPPER_MOVES) : PAIR_ZIPPER_MOVES =
struct
structure M1 = Zipper_Moves_Bi_Zipper_Moves(PM.M1)
structure M2 = Zipper_Moves_Bi_Zipper_Moves(PM.M2)
structure M = Zipper_Moves_Bi_Zipper_Moves(PM)
open M
end

functor Pair_Zipper_Moves(
    structure A : IARROW_BASE
    structure M1 : ZIPPER_MOVES
    sharing type M1.C.cat = A.cat
    structure M2 : ZIPPER_MOVES
    sharing type M1.C.cat = M2.C.cat
  ) : PAIR_ZIPPER_MOVES =
struct

structure CA =
struct
  structure M = Move_Base(M1.C)
  open M
  type ('i, 'a, 'b) init_content = 'a
  type ('i, 'a, 'b) up_content = 'a
  type ('i, 'a, 'b) down_content = 'a
  type ('i, 'a, 'b) left_content = 'a
  type ('i, 'a, 'b) right_content = 'a
end

structure PM = Pair_Zipper_Moves_Pair_Bi_Zipper_Moves(Pair_Bi_Zipper_Moves(
  structure A = A
  structure Base = struct structure CA = CA end
  structure M1 = Bi_Zipper_Moves_Zipper_Moves(open Base; structure M = M1)
  structure M2 = Bi_Zipper_Moves_Zipper_Moves(open Base; structure M = M2))
)
open PM

end
