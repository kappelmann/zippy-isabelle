(*  Title:      HOCLP/replace_move_from_to.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From"\<close>(
    structure M : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    type @{T_args} nfrom
    val dest_nfrom : (@{ParaT_args}, @{T_args} nfrom, @{T_args} M.from) M.move
  )
  : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    where type @{T_args} from = @{T_args} nfrom
    where type @{T_args} to = @{T_args} M.to
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
struct
  structure Min = M
  open M
  type @{T_args} from = @{T_args} nfrom
  fun move x = x |> Min.comp Min.move dest_nfrom
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_To"\<close>(
    structure M : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    type @{T_args} nto
    val nto : (@{ParaT_args}, @{T_args} M.to, @{T_args} nto) M.move
  )
  : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    where type @{T_args} from = @{T_args} M.from
    where type @{T_args} to = @{T_args} nto
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
struct
  structure Min = M
  open M
  type @{T_args} to = @{T_args} nto
  fun move x = x |> Min.comp nto Min.move
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
    structure M : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    type @{T_args} nfrom
    val dest_nfrom : (@{ParaT_args}, @{T_args} nfrom, @{T_args} M.from) M.move
    type @{T_args} nto
    val nto : (@{ParaT_args}, @{T_args} M.to, @{T_args} nto) M.move
  )
  : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
    where type @{T_args} from = @{T_args} nfrom
    where type @{T_args} to = @{T_args} nto
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_To"\<close>(
  type @{T_args} nto = @{T_args} nto
  val nto = nto
  structure M = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From"\<close>(
    type @{T_args} nfrom = @{T_args} nfrom
    val dest_nfrom = dest_nfrom
    structure M = M
))
