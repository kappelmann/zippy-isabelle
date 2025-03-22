(*  Title:      HOCLP/move.ML
    Author:     Kevin Kappelmann

*)
signature \<^eval>\<open>sfx_T_nargs "MOVE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} from
  type @{AllT_args} to
  val move : (@{ParaT_args} @{AllT_args} from, @{AllT_args} to) move
end

signature \<^eval>\<open>sfx_T_nargs "HOM_MOVE"\<close> =
sig
  include \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type from = to
end

functor \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    type @{AllT_args} data
    val move : (@{ParaT_args} @{AllT_args} data) M.hom_move
  ) : \<^eval>\<open>sfx_T_nargs "HOM_MOVE"\<close> =
struct
open M
type @{AllT_args} from = @{AllT_args} data
type @{AllT_args} to = @{AllT_args} data
val move = move
end

functor \<^eval>\<open>sfx_T_nargs "Instantiate_Move"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure M : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    where type @{AllT_args} from = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) M.from
    where type @{AllT_args} to = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) M.to
    where type (@{ParaT_args} 'a) K.M.t = (@{ParaT_args} 'a) M.K.M.t
  = M
