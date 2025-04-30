(*  Title:      Zippy/modify_move.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Move_From"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    type @{AllT_args} nfrom
    val dest_nfrom : (@{ParaT_args} @{AllT_args} nfrom, @{AllT_args} M.from) M.move
  ) :
    \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    where type @{AllT_args} from = @{AllT_args} nfrom
    where type @{AllT_args} to = @{AllT_args} M.to
  =
struct
structure Min = M
open M
type @{AllT_args} from = @{AllT_args} nfrom
fun move x = x |> Min.comp Min.move dest_nfrom
end

functor \<^eval>\<open>sfx_T_nargs "Modify_Move_To"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    type @{AllT_args} nto
    val nto : (@{ParaT_args} @{AllT_args} M.to, @{AllT_args} nto) M.move
  ) :
    \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    where type @{AllT_args} from = @{AllT_args} M.from
    where type @{AllT_args} to = @{AllT_args} nto
  =
struct
structure Min = M
open M
type @{AllT_args} to = @{AllT_args} nto
fun move x = x |> Min.comp nto Min.move
end

functor \<^eval>\<open>sfx_T_nargs "Modify_Move_From_To"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    type @{AllT_args} nfrom
    val dest_nfrom : (@{ParaT_args} @{AllT_args} nfrom, @{AllT_args} M.from) M.move
    type @{AllT_args} nto
    val nto : (@{ParaT_args} @{AllT_args} M.to, @{AllT_args} nto) M.move
  ) :
    \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
    where type @{AllT_args} from = @{AllT_args} nfrom
    where type @{AllT_args} to = @{AllT_args} nto
  =
\<^eval>\<open>sfx_T_nargs "Modify_Move_To"\<close>(
  type @{AllT_args} nto = @{AllT_args} nto
  val nto = nto
  structure M = \<^eval>\<open>sfx_T_nargs "Modify_Move_From"\<close>(
    type @{AllT_args} nfrom = @{AllT_args} nfrom
    val dest_nfrom = dest_nfrom
    structure M = M
))
