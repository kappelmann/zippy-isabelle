(*  Title:      HOCLP/modify_node_succ.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>suffix (string_of_int (T_Args.Poly_nargs () - 1)) "Node" ^
    T_Args.suffix_Poly_nargs "_Node"\<close>(
    structure N : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
  ) :
    \<^eval>\<open>suffix (string_of_int (T_Args.Poly_nargs () - 1)) "NODE"\<close>
    where type @{T_args} content = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.content
    where type @{T_args} next = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.next
    where type @{T_args} node = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.node
  =
struct
open N
type @{T_args} content = (@{ParaT_args},
  \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.content
type @{T_args} next = (@{ParaT_args},
  \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.next
type @{T_args} node = (@{ParaT_args},
  \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.node
end