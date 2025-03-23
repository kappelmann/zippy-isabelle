(*  Title:      Zippy/alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "LINKED_ZIPPER"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  where type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  where type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>
  where start = \<open>ML_Gen.nzippers ()\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  where type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  where type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>
  where stop = 1\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MOVES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure ZO{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) Z.Z{i}.cat
    sharing type ZO{i}.zipper = Z.Z{i}.zipper
    sharing type ZO{i}.L.lens = ZO1.L.lens\<close>\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
struct

open Z
structure LZ = \<^eval>\<open>pfx_sfx_nargs "Linked_Zipper"\<close>(
  structure Z = Z
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZO{i} = ZO{i}\<close>\<close>)
open LZ

end

functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{AllT_args} Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  = Z
