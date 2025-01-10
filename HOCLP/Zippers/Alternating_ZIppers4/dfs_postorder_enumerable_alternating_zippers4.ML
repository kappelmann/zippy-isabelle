(*  Title:      HOCLP/dfs_postorder_enumerable_alternating_zippers4.ML
    Author:     Kevin Kappelmann
*)
signature DFS_POSTORDER_ENUMERABLE_ALTERNATING_ZIPPERS4 =
sig
end

functor DFS_Postorder_Enumerable_Alternating_Zippers4(
  structure AE : KLEISLI_ARROW_EXCEPTION_REC
  structure AZ : ALTERNATING_ZIPPERS4
  sharing type AZ.Z1.M.t = AE.K.M.t

  structure E1 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.zipper
  sharing type E1.M.t = AE.K.M.t
  structure E2 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.zipper
  sharing type E2.M.t = AE.K.M.t
  structure E3 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.zipper
  sharing type E3.M.t = AE.K.M.t
  structure E4 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.zipper
  sharing type E4.M.t = AE.K.M.t
) =
struct

local structure SC = Semi_Category(AE) open SC AE
in

fun first1 x = x |> (E1.First.move >>> next1)
and first2 x = x |> (E2.First.move >>> next2)
and first3 x = x |> (E3.First.move >>> next3)
and first4 x = x |> (E4.First.move >>> next4)
and next1 x = x |> try (AZ.Down1.move >>> AZ.Z2.ZM.Unzip.move >>> first2)
and next2 x = x |> try_step (AZ.Down2.move >>> AZ.Z3.ZM.Unzip.move >>> first3) E2.Next.move
and next3 x = x |> try_step (AZ.Down3.move >>> AZ.Z4.ZM.Unzip.move >>> first4) E3.Next.move
and next4 x = x |> try_step (AZ.Down4.move >>> AZ.Z1.ZM.Unzip.move >>> first1) E4.Next.move

fun next x = x |>
  (catch' (E1.Next.move >>> next1)
  (AZ.Up1.move >>> catch' (E4.Next.move >>> next4)
  (AZ.Up4.move >>> catch' (E3.Next.move >>> next3)
  (AZ.Up3.move >>> catch' (E2.Next.move >>> next2)
  AZ.Up2.move))))

(* fun prev x = x |> AZ.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move)) *)

end

end
