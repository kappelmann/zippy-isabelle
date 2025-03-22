(*  Title:      Zippy/dfs_postorder_enumerable_alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>mk_name ["DFS_POSTORDER_ENUMERABLE", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close> =
sig
  structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val first{i} : (@{ParaT_args} @{AllT_args} Z.Z{i}.ZM.container, @{AllT_args} Z.Z1.zipper) Z.cat
  val next_no_up{i} : (@{ParaT_args} @{AllT_args} Z.Z{i}.zipper, @{AllT_args} Z.Z1.zipper) Z.cat
  \<close>\<close>
  val next : (@{ParaT_args} @{AllT_args} Z.Z1.zipper) Z.hom_move
end

functor \<^eval>\<open>mk_name ["DFS_Postorder_Enumerable", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    sharing type Z.M.t = AE.K.M.t

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure E{i} : \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close>
    where type @{AllT_args} init_data = @{AllT_args} Z.Z{i}.ZM.container
    where type @{AllT_args} data = @{AllT_args} Z.Z{i}.zipper
    sharing type E{i}.M.t = AE.K.M.t\<close>\<close>
  ) : \<^eval>\<open>mk_name ["DFS_POSTORDER_ENUMERABLE", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close>
  =
struct

structure Z = Z

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE) open SC AE
in

fun first1 x = x |> (E1.First.move >>> next_no_up1)
and next_no_up1 x = x |> try (
  Z.Down1.move
  >>> \<^eval>\<open>implode ["Z.Z", succ_mod_nzippers 1, ".ZM.Unzip.move"]\<close>
  >>> \<^eval>\<open>"first" ^ succ_mod_nzippers 1\<close>)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and first{i} x = x |> (E{i}.First.move >>> next_no_up{i})
and next_no_up{i} x = x |> try_step
  (Z.Down{i}.move
  >>> Z.Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Unzip.move
  >>> first\<^eval>\<open>succ_mod_nzippers {i}\<close>)
  E{i}.Next.move\<close>
where start = 2\<close>

(*FIXME: rather complicated, but works*)
fun next x = x |>
  (catch' (E1.Next.move >>> next_no_up1)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  (Z.Up\<^eval>\<open>succ_mod_nzippers (ML_Gen.ZipperT_nargs () + 2 - {i}) ^ "."\<close>move
  >>> catch' (E\<^eval>\<open>string_of_int (ML_Gen.ZipperT_nargs () + 2 - {i}) ^ "."\<close>Next.move
    >>> next_no_up\<^eval>\<open>string_of_int (ML_Gen.ZipperT_nargs () + 2 - {i})\<close>)\<close>
  where start = 2\<close>
  \<^eval>\<open>implode ["Z.Up", succ_mod_nzippers 1, ".move"]\<close>
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
