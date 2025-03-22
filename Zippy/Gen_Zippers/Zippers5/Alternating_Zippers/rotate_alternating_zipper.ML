(*  Title:      Zippy/rotate_alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>mk_name ["Rotate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  ) :
  \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZO.content =
    @{AllT_args} Z.Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZO.content
  where type @{AllT_args} Z{i}.ZO.zcontext =
    @{AllT_args} Z.Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZO.zcontext
  where type @{AllT_args} Z{i}.ZM.container =
    @{AllT_args} Z.Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container
  where type @{AllT_args} Z{i}.zipper =
    @{AllT_args} Z.Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper\<close>\<close>
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  =
struct
structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = Z
open M
structure L = Z.L
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = Z.Z\<^eval>\<open>succ_mod_nzippers {i}\<close>
structure Down{i} = Z.Down\<^eval>\<open>succ_mod_nzippers {i}\<close>
structure Up{i} = Z.Up\<^eval>\<open>succ_mod_nzippers {i}\<close>
\<close>\<close>
end
