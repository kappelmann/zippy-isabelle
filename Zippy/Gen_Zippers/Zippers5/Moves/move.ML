(*  Title:      HOCLP/move.ML
    Author:     Kevin Kappelmann

See typeclass_base.ML in ML_Typeclasses for an explanation of the 'p1 type variables.
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close> =
sig
  include MOVE_BASE
  type @{T_args} from
  type @{T_args} to
  val move : (@{ParaT_args}, @{T_args} from, @{T_args} to) move
end

signature \<^eval>\<open>T_Args.suffix_Poly_nargs "HOM_MOVE"\<close> =
sig
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type from = to
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(
    structure M : MOVE_BASE
    type @{T_args} data
    val move : (@{ParaT_args}, @{T_args} data) M.hom_move
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "HOM_MOVE"\<close> =
struct
open M
type @{T_args} from = @{T_args} data
type @{T_args} to = @{T_args} data
val move = move
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Move"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure M : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    where type @{T_args} from = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) M.from
    where type @{T_args} to = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) M.to
    where type ('p1, 'a) K.M.t = ('p1, 'a) M.K.M.t
  = M
