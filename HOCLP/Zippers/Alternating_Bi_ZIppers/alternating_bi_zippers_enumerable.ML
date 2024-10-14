(*  Title:      HOCLP/alternating_bi_zippers_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature TEST =
sig
end

functor Test(
  structure AE : LAZY_IARROW_EXCEPTION
  structure AZ : ALTERNATING_BI_ZIPPERS
  where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AE.cat

  structure E1 : BI_ENUMERABLE
  where type ('i, 'a, 'b) init_data = ('i, 'a, 'b) AZ.Z1.container
  where type ('i, 'a, 'b) data = ('i, 'a, 'b) AZ.Z1.zipper
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat

  structure E2 : BI_ENUMERABLE
  where type ('i, 'a, 'b) init_data = ('i, 'a, 'b) AZ.Z2.container
  where type ('i, 'a, 'b) data = ('i, 'a, 'b) AZ.Z2.zipper
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat
) =
struct

local structure SC = ISemi_Category(AE) open SC AE
in

fun down_init down_move unzip init_move = init_move o arr unzip o down_move

fun try_step f step = catch' f (comp_lazy (fn _ => try_step f step) step)

fun first1 _ = (comp_lazy (fn _ => next1) E1.First.move) ()
and first2 _ = (next2 o E2.First.move) ()
and next1 _ = try (first2 o arr AZ.Z2.unzip o AZ.Down1.move) ()
and next2 _ = try_step (first1 o arr AZ.Z1.unzip o AZ.Down2.move) E2.Next.move ()

fun next _ = catch' (next1 o E1.Next.move)
  (catch' (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move))
  ()

(* fun prev x = x |> AZ.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move)) *)

end

end
