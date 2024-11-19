(*  Title:      HOCLP/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor Int_Enumerable4(
    structure A : LAZY_ARROW_BASE
    structure M : MOVE_BASE
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.cat
  ) : ENUMERABLE4 where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M.cat
  = Enumerable4(
  structure M = M
  type ('i, 'a1, 'a2, 'a3, 'a4) init_data = int
  type ('i, 'a1, 'a2, 'a3, 'a4) data = int
  fun first _ = A.id ()
    |> Lazy_Cat_Util.unlift
  fun next _ = A.arr (fn p => p + 1)
    |> Lazy_Cat_Util.unlift
  fun prev _ = A.arr (fn p => p - 1)
    |> Lazy_Cat_Util.unlift
)