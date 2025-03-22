(*  Title:      HOCLP/modify_node_succ.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Node_Succ"\<close>(
    structure N : \<^eval>\<open>succ_node_sig\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.content
    where type @{AllT_args} next = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.next
    where type @{AllT_args} node = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.node
  =
struct
open N
type @{AllT_args} content = (@{ParaT_args}
  \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.content
type @{AllT_args} next = (@{ParaT_args}
  \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.next
type @{AllT_args} node = (@{ParaT_args}
  \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.node
end