(*  Title:      HOCLP/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor Int_Enumerable(
    structure A : IARROW_BASE
    structure M : MOVE_BASE
    sharing type M.C.cat = A.cat
  ) : ENUMERABLE = Enumerable(
  structure M = M
  type ('i, 'a) init_data = int
  type ('i, 'a) data = int
  val first = A.id
  fun next _ = A.arr (fn p => p + 1)
  fun prev _ = A.arr (fn p => p - 1)
)