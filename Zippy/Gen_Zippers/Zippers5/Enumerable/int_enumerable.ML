(*  Title:      HOCLP/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Int_Enumerable"\<close>(
    structure M : MOVE_BASE
    type @{T_args} init_data
    val first : (@{ParaT_args}, @{T_args} init_data, int) M.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close>
    where type @{T_args} init_data = @{T_args} init_data
    where type @{T_args} data = int
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  = \<^eval>\<open>T_Args.suffix_Poly_nargs "Enumerable"\<close>(
  structure M = M
  type @{T_args} init_data = @{T_args} init_data
  type @{T_args} data = int
  val first = first
  fun next x = x |> M.arr (fn p => p + 1)
  fun prev x = x |> M.arr (fn p => p - 1)
)