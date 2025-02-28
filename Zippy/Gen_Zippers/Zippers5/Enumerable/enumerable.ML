(*  Title:      HOCLP/enumerable.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close> =
sig
  include MOVE_BASE
  type @{T_args} init_data
  type @{T_args} data

  structure First : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type First.from = init_data
  sharing type First.to = data
  sharing type First.M.t = M.t

  structure Next : \<^eval>\<open>T_Args.suffix_Poly_nargs "HOM_MOVE"\<close>
  sharing type Next.from = data
  sharing type Next.M.t = M.t

  structure Prev : \<^eval>\<open>T_Args.suffix_Poly_nargs "HOM_MOVE"\<close>
  sharing type Prev.from = data
  sharing type Prev.M.t = M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Enumerable"\<close>(
    structure M : MOVE_BASE
    type @{T_args} init_data
    type @{T_args} data
    val first : (@{ParaT_args}, @{T_args} init_data, @{T_args} data) M.move
    val next : (@{ParaT_args}, @{T_args} data) M.hom_move
    val prev: (@{ParaT_args}, @{T_args} data) M.hom_move
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close> =
struct

structure Min = M
open M
type @{T_args} init_data = @{T_args} init_data
type @{T_args} data = @{T_args} data

structure First =
struct
  open Min
  type @{T_args} from = @{T_args} init_data
  type @{T_args} to = @{T_args} data
  val move = first
end

structure Base = struct
  structure M = Min
  type @{T_args} data = @{T_args} data
end
structure Next = \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(
  open Base; val move = next)
structure Prev = \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(
  open Base; val move = prev)

end

signature \<^eval>\<open>T_Args.suffix_Poly_nargs "LAST_ENUMERABLE"\<close> =
sig
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close>
  structure Last : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Last.from = init_data
  sharing type Last.to = data
  sharing type Last.M.t = M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Last_Enumerable"\<close>(
    structure E : \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close>
    val last : (@{ParaT_args}, @{T_args} E.init_data, @{T_args} E.data) E.move
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "LAST_ENUMERABLE"\<close> =
struct
open E

structure Last =
struct
  open E
  type @{T_args} from = @{T_args} init_data
  type @{T_args} to = @{T_args} data
  val move = last
end

end
