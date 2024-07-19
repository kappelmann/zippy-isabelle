(*  Title:      HOCLP/pair_bi_move.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_BI_MOVE =
sig
  structure M1 : BI_MOVE
  structure M2 : BI_MOVE
  sharing type M1.K.M.t = M2.K.M.t

  include BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) M1.from * ('i, 'a, 'b) M2.from
  where type ('i, 'a, 'b) to = ('i, 'a, 'b) M1.to * ('i, 'a, 'b) M2.to
  sharing type M1.K.M.t = K.M.t
  sharing type M2.K.M.t = K.M.t
end

functor Pair_Bi_Move(
    structure M1 : BI_MOVE
    structure M2 : BI_MOVE
    sharing type M1.K.M.t = M2.K.M.t
  ) : PAIR_BI_MOVE =
struct

structure M1 = M1
structure M2 = M2

structure M = Move_Base(M1.K)
open M

type ('i, 'a, 'b) from = ('i, 'a, 'b) M1.from * ('i, 'a, 'b) M2.from
type ('i, 'a, 'b) to = ('i, 'a, 'b) M1.to * ('i, 'a, 'b) M2.to

structure A = IKleisli_IArrow_Apply(M1.K.M)
fun move x = x |> A.*** (M1.move, M2.move)

end
