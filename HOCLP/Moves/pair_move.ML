(*  Title:      HOCLP/pair_move.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_MOVE =
sig
  structure M1 : MOVE
  structure M2 : MOVE
  sharing type M1.K.M.t = M2.K.M.t

  include MOVE
  where type ('i, 'a) from = ('i, 'a) M1.from * ('i, 'a) M2.from
  where type ('i, 'a) to = ('i, 'a) M1.to * ('i, 'a) M2.to
  sharing type M1.K.M.t = K.M.t
  sharing type M2.K.M.t = K.M.t
end

functor Pair_Bi_Move_Pair_Move(type ('i, 'a, 'b) content; structure PM : PAIR_MOVE) : PAIR_BI_MOVE =
struct
structure Base = struct type ('i, 'a, 'b) content = ('i, 'a, 'b) content end
structure M1 = Bi_Move_Move(open Base; structure M = PM.M1)
structure M2 = Bi_Move_Move(open Base; structure M = PM.M2)
structure M = Bi_Move_Move(open Base; structure M = PM)
open M
end

functor Pair_Move_Pair_Bi_Move(PM : PAIR_BI_MOVE) : PAIR_MOVE =
struct
structure M1 = Move_Bi_Move(PM.M1)
structure M2 = Move_Bi_Move(PM.M2)
structure M = Move_Bi_Move(PM)
open M
end

functor Pair_Move(
    structure M1 : MOVE
    structure M2 : MOVE
    sharing type M1.K.M.t = M2.K.M.t
  ) : PAIR_MOVE =
Pair_Move_Pair_Bi_Move(Pair_Bi_Move(
  structure Base = struct type ('i, 'a, 'b) content = 'a end
  structure M1 = Bi_Move_Move(open Base; structure M = M1)
  structure M2 = Bi_Move_Move(open Base; structure M = M2)
))
