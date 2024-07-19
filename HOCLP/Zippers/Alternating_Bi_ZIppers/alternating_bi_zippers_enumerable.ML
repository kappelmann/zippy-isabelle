(*  Title:      HOCLP/alternating_bi_zippers_enumerable.ML
    Author:     Kevin Kappelmann
*)
signature TEST =
sig
end

functor Test(
  structure AZ : ALTERNATING_BI_ZIPPERS

  structure E1 : BI_ENUMERABLE
  where type ('i, 'a, 'b) init_data = ('i, 'a, 'b) AZ.Z1.container
  where type ('i, 'a, 'b) data = ('i, 'a, 'b) AZ.Z1.zipper
  sharing type E1.K.M.t = AZ.Z1.K.M.t
  sharing type E1.K.M.t = AZ.Z2.K.M.t
  sharing type E1.K.M.t = AZ.Up1.K.M.t
  sharing type E1.K.M.t = AZ.Up2.K.M.t

  structure E2 : BI_ENUMERABLE
  where type ('i, 'a, 'b) init_data = ('i, 'a, 'b) AZ.Z2.container
  where type ('i, 'a, 'b) data = ('i, 'a, 'b) AZ.Z2.data
  sharing type E2.K.M.t = E1.K.M.t

  structure ME : IMONAD_EXCEPTION_BASE
  sharing type ME.t = E1.K.M.t
) =
struct

structure MU = Move_Util(ME)

local open MU.C MU.AE
in

fun down_init down_move unzip init_move x = x |> (unzip #> init_move) o down_move

fun try_step move step x = x |> catch' move (try_step move step o step)

fun first1 x = x |> next1 o E1.First.move
and first2 x = x |> next2 o E2.First.move
and next1 x = x |> try (first2 o arr AZ.Z2.unzip o AZ.Down1.move)
and next2 x = x |> try_step (first1 o arr AZ.Z1.unzip o AZ.Down2.move) E2.Next.move

fun next x = x |> catch' (next1 o E1.Next.move)
  (catch' (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move))

(* fun prev x = x |> AZ.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o AZ.Up1.move) (AZ.Up2.move o AZ.Up1.move)) *)

end

end
