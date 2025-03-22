(*  Title:      HOCLP/zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} zipper
  structure ZM : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  sharing type ZM.zipper = zipper
  sharing type ZM.M.t = M.t
  structure ZO : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) cat
  sharing type ZO.zipper = zipper
end

functor \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
    structure ZM : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    structure ZO : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) ZM.cat
    sharing type ZO.zipper = ZM.zipper
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
struct

structure ZM = ZM
structure ZO = ZO
open ZM

end

functor \<^eval>\<open>sfx_T_nargs "Instantiate_Zipper"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.ZM.container
    where type @{AllT_args} ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.ZO.content
    where type @{AllT_args} ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.ZO.zcontext
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  = Z
