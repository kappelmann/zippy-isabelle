(*  Title:      HOCLP/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor Int_Enumerable4(
    structure M : MOVE_BASE
  ) : ENUMERABLE4 where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  = Enumerable4(
  structure M = M
  type ('i, 'a1, 'a2, 'a3, 'a4) init_data = int
  type ('i, 'a1, 'a2, 'a3, 'a4) data = int
  fun first x = x |> M.id ()
  fun next x = x |> M.arr (fn p => p + 1)
  fun prev x = x |> M.arr (fn p => p - 1)
)