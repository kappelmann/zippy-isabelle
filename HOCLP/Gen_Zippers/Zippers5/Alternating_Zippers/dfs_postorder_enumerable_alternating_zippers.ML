(*  Title:      HOCLP/dfs_postorder_enumerable_alternating_zippers.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_POSTORDER_ENUMERABLE_ALTERNATING_ZIPPERS"\<close> =
sig
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable_Alternating_Zippers"\<close>(
    structure AE : KLEISLI_ARROW_EXCEPTION_REC
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    sharing type Z.M.t = AE.K.M.t

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure E{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close>
    where type @{T_args} init_data = @{T_args} Z.Z{i}.ZM.container
    where type @{T_args} data = @{T_args} Z.Z{i}.zipper
    sharing type E{i}.M.t = AE.K.M.t\<close>\<close>
  )
  (*TODO: signaute*)
  (* : \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_POSTORDER_ENUMERABLE_ALTERNATING_ZIPPERS"\<close> *)
  =
struct

local structure SC = Semi_Category(AE) open SC AE
in

fun first1 x = x |> (E1.First.move >>> next1)
and next1 x = x |> try (
  Z.Down1.move
  >>> \<^eval>\<open>implode ["Z.Z", T_Args.succ_mod_Poly_nargs' 1, ".ZM.Unzip.move"]\<close>
  >>> \<^eval>\<open>"first" ^ T_Args.succ_mod_Poly_nargs' 1\<close>)
and \<^imap>\<open>\<open>{i}\<close> => \<open>
first{i} x = x |> (E{i}.First.move >>> next{i})
and next{i} x = x |> try_step (
    Z.Down{i}.move
    >>> Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.Unzip.move
    >>> first\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>)
  E{i}.Next.move\<close>
where start = 2 and sep = "and"\<close>

(*FIXME: rather complicated, but works*)
fun next x = x |>
  (catch' (E1.Next.move >>> next1)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  (Z.Up\<^eval>\<open>T_Args.succ_mod_Poly_nargs' (T_Args.Poly_nargs () + 2 - {i}) ^ "."\<close>move
  >>> catch' (E\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 2 - {i}) ^ "."\<close>Next.move
    >>> next\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 2 - {i})\<close>)\<close>
  where start = 2\<close>
  \<^eval>\<open>implode ["Z.Up", T_Args.succ_mod_Poly_nargs' 1, ".move"]\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>)\<close> where start = 2\<close>)

(*instance example for n = 5*)
(* fun next x = x |>
  (catch' (E1.Next.move >>> next1)
  (Z.Up1.move >>> catch' (E5.Next.move >>> next5)
  (Z.Up5.move >>> catch' (E4.Next.move >>> next4)
  (Z.Up4.move >>> catch' (E3.Next.move >>> next3)
  (Z.Up3.move >>> catch' (E2.Next.move >>> next2)
  Z.Up2.move))))) *)

(* fun prev x = x |> Z.Down1.move *)
  (* or (next1 o E1.Prev.move) *)
  (* (or (next2 o E2.Next.move o Z.Up1.move) (Z.Up2.move o Z.Up1.move)) *)

end

end
