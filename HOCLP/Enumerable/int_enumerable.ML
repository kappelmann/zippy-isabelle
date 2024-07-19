(*  Title:      HOCLP/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor Int_Enumerable(M : MOVE_BASE) : ENUMERABLE = Enumerable(
  structure M = M
  structure A = IArrow(IKleisli_IArrow_Apply(M.K.M))
  type ('i, 'a) init_data = int
  type ('i, 'a) data = int
  fun first x = A.id () x
  fun next x = A.arr (fn p => p + 1) x
  fun prev x = A.arr (fn p => p - 1) x
)