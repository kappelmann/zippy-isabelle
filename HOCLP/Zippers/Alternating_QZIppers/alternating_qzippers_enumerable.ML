(*  Title:      HOCLP/alternating_qzippers_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature TEST =
sig
end

functor Test(
  structure AE : LAZY_IARROW_EXCEPTION_REC
  structure L : ILAZY_COMP
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat
  structure AZ : ALTERNATING_QZIPPERS
  where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Down3.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Down4.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) AE.cat
  where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) AE.cat

  structure E1 : QENUMERABLE
  where type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) AZ.Z1.container
  where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) AZ.Z1.zipper
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat
  structure E2 : QENUMERABLE
  where type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) AZ.Z2.container
  where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) AZ.Z2.zipper
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat
  structure E3 : QENUMERABLE
  where type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) AZ.Z3.container
  where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) AZ.Z3.zipper
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat
  structure E4 : QENUMERABLE
  where type ('i, 'a, 'b, 'c, 'd) init_data = ('i, 'a, 'b, 'c, 'd) AZ.Z4.container
  where type ('i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd) AZ.Z4.zipper
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) AE.cat

) =
struct

local structure SC = ISemi_Category(AE) open SC AE
in

fun down_init down_move unzip init_move = init_move o arr unzip o down_move

fun first1 _ = (L.comp_lazy (fn _ => next1) E1.First.move) ()
and first2 _ = (next2 o E2.First.move) ()
and first3 _ = (next3 o E3.First.move) ()
and first4 _ = (next4 o E4.First.move) ()
and next1 _ = try (first2 o arr AZ.Z2.unzip o AZ.Down1.move) ()
and next2 _ = try_step (first3 o arr AZ.Z3.unzip o AZ.Down2.move) E2.Next.move ()
and next3 _ = try_step (first4 o arr AZ.Z4.unzip o AZ.Down3.move) E3.Next.move ()
and next4 _ = try_step (first1 o arr AZ.Z1.unzip o AZ.Down4.move) E4.Next.move ()

fun next _ = catch' (E1.Next.move >>> next1)
  (AZ.Up1.move >>> catch' (E4.Next.move >>> next4)
  (AZ.Up4.move >>> catch' (E3.Next.move >>> next3)
  (AZ.Up3.move >>> catch' (E2.Next.move >>> next2)
  AZ.Up2.move)))
  ()

(* fun prev x = x |> AZ.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move)) *)

end

end
