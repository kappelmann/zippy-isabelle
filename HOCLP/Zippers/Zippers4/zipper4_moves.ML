(*  Title:      HOCLP/zipper4_moves.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER4_MOVES =
sig
  include MOVE_BASE
  type ('p1, 'a1, 'a2, 'a3, 'a4) container
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper

  structure Zip : MOVE4
  sharing type Zip.from = container
  sharing type Zip.to = zipper
  sharing type Zip.M.t = M.t
  structure Unzip : MOVE4
  sharing type Unzip.from = zipper
  sharing type Unzip.to = container
  sharing type Unzip.M.t = M.t

  structure Up : MOVE4
  sharing type Up.from = zipper
  sharing type Up.to = zipper
  sharing type Up.M.t = M.t
  structure Down : MOVE4
  sharing type Down.from = zipper
  sharing type Down.to = zipper
  sharing type Down.M.t = M.t
  structure Left : MOVE4
  sharing type Left.from = zipper
  sharing type Left.to = zipper
  sharing type Left.M.t = M.t
  structure Right : MOVE4
  sharing type Right.from = zipper
  sharing type Right.to = zipper
  sharing type Right.M.t = M.t
end

functor Zipper4_Moves(
    structure M : MOVE_BASE
    type ('p1, 'a1, 'a2, 'a3, 'a4) container
    type ('p1, 'a1, 'a2, 'a3, 'a4) zipper
    val zip : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) container, ('p1, 'a1, 'a2, 'a3, 'a4) zipper) M.move
    val unzip : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper, ('p1, 'a1, 'a2, 'a3, 'a4) container) M.move
    val up : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper) M.hom_move
    val down : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper) M.hom_move
    val left : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper) M.hom_move
    val right : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper) M.hom_move
  ) : ZIPPER4_MOVES =
struct

structure Min = M
open M
type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, 'a1, 'a2, 'a3, 'a4) container
type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) zipper

structure Zip =
struct
  open Min
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) container
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) zipper
  val move = zip
end
structure Unzip =
struct
  open Min
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) container
  val move = unzip
end

structure Base =
  struct structure M = Min; type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) zipper end
structure Up = Hom_Move4(open Base; val move = up)
structure Down = Hom_Move4(open Base; val move = down)
structure Left = Hom_Move4(open Base; val move = left)
structure Right = Hom_Move4(open Base; val move = right)

end

functor Instantiate_Zipper4_Moves(
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4) inst4
    structure Z : ZIPPER4_MOVES
  ) :
    ZIPPER4_MOVES
    where type ('p1, 'a1, 'a2, 'a3, 'a4) container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst2, ('p1, 'a1, 'a2, 'a3, 'a4) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4) inst4) Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  = Z

