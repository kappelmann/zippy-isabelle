(*  Title:      HOCLP/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor Int_Enumerable(
    structure A : LAZY_IARROW_BASE
    structure M : MOVE_BASE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
  ) : ENUMERABLE where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  = Enumerable(
  structure M = M
  type ('i, 'a) init_data = int
  type ('i, 'a) data = int
  fun first _ = A.id () ()
  fun next _ = A.arr (fn p => p + 1) ()
  fun prev _ = A.arr (fn p => p - 1) ()
)