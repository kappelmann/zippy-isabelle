(*  Title:      Zippy/modify_alternating_zipper_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>mk_name ["Modify", pfx_sfx_nargs "Alternating_Zipper_Zipper"]\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} nzipper{i}
    val nzipper{i} : (@{ParaT_args} @{AllT_args} Z.Z{i}.zipper, @{AllT_args} nzipper{i}) Z.cat
    val dest_nzipper{i} : (@{ParaT_args} @{AllT_args} nzipper{i}, @{AllT_args} Z.Z{i}.zipper) Z.cat\<close>\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZD.content = @{AllT_args} Z.Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = @{AllT_args} Z.Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.zipper = @{AllT_args} nzipper{i}\<close>\<close>
  =
struct

structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = Z
open M
structure L = Z.L

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Zipper"\<close>(
  structure Z = Z.Z{i}
  type @{AllT_args} nzipper = @{AllT_args} nzipper{i}
  val nzipper = nzipper{i}
  val dest_nzipper = dest_nzipper{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = \<^eval>\<open>sfx_T_nargs "Modify_Move_From_To"\<close>(
  structure M = Z.Down{i}
  type @{AllT_args} nfrom = @{AllT_args} nzipper{i}
  type @{AllT_args} nto = @{AllT_args} nzipper\<^eval>\<open>succ_mod_nzippers {i}\<close>
  val dest_nfrom = dest_nzipper{i}
  val nto = nzipper\<^eval>\<open>succ_mod_nzippers {i}\<close>
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = \<^eval>\<open>sfx_T_nargs "Modify_Move_From_To"\<close>(
  structure M = Z.Up{i}
  type @{AllT_args} nfrom = @{AllT_args} nzipper{i}
  type @{AllT_args} nto = @{AllT_args} nzipper\<^eval>\<open>pred_mod_nzippers {i}\<close>
  val dest_nfrom = dest_nzipper{i}
  val nto = nzipper\<^eval>\<open>pred_mod_nzippers {i}\<close>
)\<close>\<close>

end