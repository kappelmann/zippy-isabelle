(*  Title:      HOCLP/dfs_postorder_enumerable_alternating_zippers.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_POSTORDER_ENUMERABLE_ALTERNATING_ZIPPERS"\<close> =
sig
  structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val first{i} : (@{ParaT_args}, @{T_args} Z.Z{i}.ZM.container, @{T_args} Z.Z1.zipper) Z.cat
  val next_no_up{i} : (@{ParaT_args}, @{T_args} Z.Z{i}.zipper, @{T_args} Z.Z1.zipper) Z.cat
  \<close>\<close>
  val next : (@{ParaT_args}, @{T_args} Z.Z1.zipper) Z.hom_move
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
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_POSTORDER_ENUMERABLE_ALTERNATING_ZIPPERS"\<close>
  =
struct

structure Z = Z

local structure SC = Semi_Category(AE) open SC AE
in

fun first1 x = x |> (E1.First.move >>> next_no_up1)
and next_no_up1 x = x |> try (
  Z.Down1.move
  >>> \<^eval>\<open>implode ["Z.Z", T_Args.succ_mod_Poly_nargs' 1, ".ZM.Unzip.move"]\<close>
  >>> \<^eval>\<open>"first" ^ T_Args.succ_mod_Poly_nargs' 1\<close>)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and first{i} x = x |> (E{i}.First.move >>> next_no_up{i})
and next_no_up{i} x = x |> try_step
  (Z.Down{i}.move
  >>> Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.Unzip.move
  >>> first\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>)
  E{i}.Next.move\<close>
where start = 2\<close>

(*FIXME: rather complicated, but works*)
fun next x = x |>
  (catch' (E1.Next.move >>> next_no_up1)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  (Z.Up\<^eval>\<open>T_Args.succ_mod_Poly_nargs' (T_Args.Poly_nargs () + 2 - {i}) ^ "."\<close>move
  >>> catch' (E\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 2 - {i}) ^ "."\<close>Next.move
    >>> next_no_up\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 2 - {i})\<close>)\<close>
  where start = 2\<close>
  \<^eval>\<open>implode ["Z.Up", T_Args.succ_mod_Poly_nargs' 1, ".move"]\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>)\<close> where start = 2\<close>)

(*instance example for n = 5*)
(* fun next x = x |>
  (catch' (E1.Next.move >>> next_no_up1)
  (Z.Up1.move >>> catch' (E5.Next.move >>> next_no_up5)
  (Z.Up5.move >>> catch' (E4.Next.move >>> next_no_up4)
  (Z.Up4.move >>> catch' (E3.Next.move >>> next_no_up3)
  (Z.Up3.move >>> catch' (E2.Next.move >>> next_no_up2)
  Z.Up2.move))))) *)

end

end
