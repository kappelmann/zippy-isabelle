(*  Title:      HOCLP/alternating_zippers4_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature TEST =
sig
end

functor Test(
  structure AE : LAZY_ARROW_EXCEPTION_REC
  structure L : LAZY_COMP
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AE.cat
  structure AZ : ALTERNATING_ZIPPERS4
  where type ('p1, 'a, 'b) Z1.cat = ('p1, 'a, 'b) AE.cat

  structure E1 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z1.zipper
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AE.cat
  structure E2 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z2.zipper
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AE.cat
  structure E3 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z3.zipper
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AE.cat
  structure E4 : ENUMERABLE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) init_data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) data = ('p1, 'a1, 'a2, 'a3, 'a4) AZ.Z4.zipper
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) AE.cat
) =
struct

local structure SC = Semi_Category(AE) open SC AE
in

fun down_init down_move unzip init_move = init_move o arr unzip o down_move

fun first1 _ = L.comp_lazy (fn _ => next1) E1.First.move
  |> Lazy_Cat_Util.unlift
and first2 _ = (next2 o E2.First.move)
  |> Lazy_Cat_Util.unlift
and first3 _ = (next3 o E3.First.move)
  |> Lazy_Cat_Util.unlift
and first4 _ = (next4 o E4.First.move)
  |> Lazy_Cat_Util.unlift
and next1 _ = try (first2 o AZ.Z2.ZM.Unzip.move o AZ.Down1.move)
  |> Lazy_Cat_Util.unlift
and next2 _ = try_step (first3 o AZ.Z3.ZM.Unzip.move o AZ.Down2.move) E2.Next.move
  |> Lazy_Cat_Util.unlift
and next3 _ = try_step (first4 o AZ.Z4.ZM.Unzip.move o AZ.Down3.move) E3.Next.move
  |> Lazy_Cat_Util.unlift
and next4 _ = try_step (first1 o AZ.Z1.ZM.Unzip.move o AZ.Down4.move) E4.Next.move
  |> Lazy_Cat_Util.unlift

fun next _ = catch' (E1.Next.move >>> next1)
  (AZ.Up1.move >>> catch' (E4.Next.move >>> next4)
  (AZ.Up4.move >>> catch' (E3.Next.move >>> next3)
  (AZ.Up3.move >>> catch' (E2.Next.move >>> next2)
  AZ.Up2.move)))
  |> Lazy_Cat_Util.unlift

(* fun prev x = x |> AZ.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move)) *)

end

end
