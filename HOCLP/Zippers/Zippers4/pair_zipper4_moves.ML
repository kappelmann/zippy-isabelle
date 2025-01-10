(*  Title:      HOCLP/pair_zipper4_moves.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ZIPPER4_MOVES =
sig
  structure Z1 : ZIPPER4_MOVES
  structure Z2 : ZIPPER4_MOVES
  sharing type Z2.M.t = Z1.M.t

  include ZIPPER4_MOVES
  where type ('p1, 'a1, 'a2, 'a3, 'a4) container =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.container * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  sharing type M.t = Z1.M.t
end

functor Pair_Zipper4_Moves(
    structure Z1 : ZIPPER4_MOVES
    structure Z2 : ZIPPER4_MOVES
    sharing type Z2.M.t = Z1.M.t
  ) : PAIR_ZIPPER4_MOVES =
struct

structure Z1 = Z1
structure Z2 = Z2

type ('p1, 'a1, 'a2, 'a3, 'a4) container =
  ('p1, 'a1, 'a2, 'a3, 'a4) Z1.container * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.container
type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
  ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper

structure M : MOVE_BASE = Z1
open M

structure Zip = Pair_Move4(structure M1 = Z1.Zip; structure M2 = Z2.Zip)
structure Unzip = Pair_Move4(structure M1 = Z1.Unzip; structure M2 = Z2.Unzip)
structure Up = Pair_Move4(structure M1 = Z1.Up; structure M2 = Z2.Up)
structure Down = Pair_Move4(structure M1 = Z1.Down; structure M2 = Z2.Down)
structure Left = Pair_Move4(structure M1 = Z1.Left; structure M2 = Z2.Left)
structure Right = Pair_Move4(structure M1 = Z1.Right; structure M2 = Z2.Right)

end

