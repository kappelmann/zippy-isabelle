(*  Title:      HOCLP/pair_move4.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_MOVE4 =
sig
  structure M1 : MOVE4
  structure M2 : MOVE4
  sharing type M1.M.t = M2.M.t

  include MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from =
    ('p1, 'a1, 'a2, 'a3, 'a4) M1.from * ('p1, 'a1, 'a2, 'a3, 'a4) M2.from
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to =
    ('p1, 'a1, 'a2, 'a3, 'a4) M1.to * ('p1, 'a1, 'a2, 'a3, 'a4) M2.to
  sharing type M1.M.t = M.t
  sharing type M2.M.t = M.t
end

functor Pair_Move4(
    structure M1 : MOVE4
    structure M2 : MOVE4
    sharing type M2.M.t = M1.M.t
  ) : PAIR_MOVE4
  =
struct

structure M1 = M1
structure M2 = M2

structure M : MOVE_BASE = M1
open M

type ('p1, 'a1, 'a2, 'a3, 'a4) from =
  ('p1, 'a1, 'a2, 'a3, 'a4) M1.from * ('p1, 'a1, 'a2, 'a3, 'a4) M2.from
type ('p1, 'a1, 'a2, 'a3, 'a4) to =
  ('p1, 'a1, 'a2, 'a3, 'a4) M1.to * ('p1, 'a1, 'a2, 'a3, 'a4) M2.to

fun move x = x |> M1.*** (M1.move, M2.move)

end
