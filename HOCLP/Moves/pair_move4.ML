(*  Title:      HOCLP/pair_move4.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_MOVE4 =
sig
  structure M1 : MOVE4
  structure M2 : MOVE4
  sharing type M1.cat = M2.cat

  include MOVE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) from =
    ('p1, 'a1, 'a2, 'a3, 'a4) M1.from * ('p1, 'a1, 'a2, 'a3, 'a4) M2.from
  where type ('p1, 'a1, 'a2, 'a3, 'a4) to =
    ('p1, 'a1, 'a2, 'a3, 'a4) M1.to * ('p1, 'a1, 'a2, 'a3, 'a4) M2.to
  sharing type M1.cat = cat
  sharing type M2.cat = cat
end

functor Pair_Move4(
    structure A : LAZY_ARROW_BASE
    structure M1 : MOVE4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.cat
    structure M2 : MOVE4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M1.cat
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

fun move _ = A.*** (M1.move, M2.move)
  |> Lazy_Cat_Util.unlift

end
