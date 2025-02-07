(*  Title:      HOCLP/dfs_postorder_enumerable_alternating_zippers5.ML
    Author:     Kevin Kappelmann
*)
signature DFS_POSTORDER_ENUMERABLE_ALTERNATING_ZIPPERS5 =
sig
end

functor DFS_Postorder_Enumerable_Alternating_Zippers5(
  structure AE : KLEISLI_ARROW_EXCEPTION_REC
  structure Z : ALTERNATING_ZIPPERS5
  sharing type Z.Z1.M.t = AE.K.M.t

  structure E1 : ENUMERABLE5
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) init_data =
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z1.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) data = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z1.zipper
  sharing type E1.M.t = AE.K.M.t
  structure E2 : ENUMERABLE5
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) init_data =
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z2.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) data = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z2.zipper
  sharing type E2.M.t = AE.K.M.t
  structure E3 : ENUMERABLE5
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) init_data =
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z3.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) data = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z3.zipper
  sharing type E3.M.t = AE.K.M.t
  structure E4 : ENUMERABLE5
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) init_data =
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z4.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) data = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z4.zipper
  sharing type E4.M.t = AE.K.M.t
  structure E5 : ENUMERABLE5
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) init_data =
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z5.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) data = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z.Z5.zipper
  sharing type E5.M.t = AE.K.M.t
) =
struct

local structure SC = Semi_Category(AE) open SC AE
in

fun first1 x = x |> (E1.First.move >>> next1)
and first2 x = x |> (E2.First.move >>> next2)
and first3 x = x |> (E3.First.move >>> next3)
and first4 x = x |> (E4.First.move >>> next4)
and first5 x = x |> (E5.First.move >>> next5)
and next1 x = x |> try (Z.Down1.move >>> Z.Z2.ZM.Unzip.move >>> first2)
and next2 x = x |> try_step (Z.Down2.move >>> Z.Z3.ZM.Unzip.move >>> first3) E2.Next.move
and next3 x = x |> try_step (Z.Down3.move >>> Z.Z4.ZM.Unzip.move >>> first4) E3.Next.move
and next4 x = x |> try_step (Z.Down4.move >>> Z.Z5.ZM.Unzip.move >>> first5) E4.Next.move
and next5 x = x |> try_step (Z.Down5.move >>> Z.Z1.ZM.Unzip.move >>> first1) E5.Next.move

fun next x = x |>
  (catch' (E1.Next.move >>> next1)
  (Z.Up1.move >>> catch' (E5.Next.move >>> next5)
  (Z.Up5.move >>> catch' (E4.Next.move >>> next4)
  (Z.Up4.move >>> catch' (E3.Next.move >>> next3)
  (Z.Up3.move >>> catch' (E2.Next.move >>> next2)
  Z.Up2.move)))))

(* fun prev x = x |> Z.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o Z.Up1.move) (Z.Up2.move o Z.Up1.move)) *)

end

end
