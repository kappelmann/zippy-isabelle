(*  Title:      Zippy/enumerable.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} init_data
  type @{AllT_args} data

  structure First : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.M.t = M.t

  structure Next : \<^eval>\<open>sfx_T_nargs "HOM_MOVE"\<close>
  sharing type Next.from = data
  sharing type Next.M.t = M.t

  structure Prev : \<^eval>\<open>sfx_T_nargs "HOM_MOVE"\<close>
  sharing type Prev.from = data
  sharing type Prev.M.t = M.t
end

functor \<^eval>\<open>sfx_T_nargs "Enumerable"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    type @{AllT_args} init_data
    type @{AllT_args} data
    val first : (@{ParaT_args} @{AllT_args} init_data, @{AllT_args} data) M.move
    val next : (@{ParaT_args} @{AllT_args} data) M.hom_move
    val prev: (@{ParaT_args} @{AllT_args} data) M.hom_move
  ) : \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close> =
struct

structure Min = M
open M
type @{AllT_args} init_data = @{AllT_args} init_data
type @{AllT_args} data = @{AllT_args} data

structure First =
struct
  open Min
  type @{AllT_args} from = @{AllT_args} init_data
  type @{AllT_args} to = @{AllT_args} data
  val move = first
end

structure Base = struct
  structure M = Min
  type @{AllT_args} data = @{AllT_args} data
end
structure Next = \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(
  open Base; val move = next)
structure Prev = \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(
  open Base; val move = prev)

end

signature \<^eval>\<open>sfx_T_nargs "LAST_ENUMERABLE"\<close> =
sig
  include \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close>
  structure Last : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.M.t = M.t
end

functor \<^eval>\<open>sfx_T_nargs "Last_Enumerable"\<close>(
    structure E : \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close>
    val last : (@{ParaT_args} @{AllT_args} E.init_data, @{AllT_args} E.data) E.move
  ) : \<^eval>\<open>sfx_T_nargs "LAST_ENUMERABLE"\<close> =
struct
open E

structure Last =
struct
  open E
  type @{AllT_args} from = @{AllT_args} init_data
  type @{AllT_args} to = @{AllT_args} data
  val move = last
end

end
