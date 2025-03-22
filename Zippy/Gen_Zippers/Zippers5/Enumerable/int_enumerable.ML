(*  Title:      Zippy/int_enumerable.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Int_Enumerable"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    type @{AllT_args} init_data
    val first : (@{ParaT_args} @{AllT_args} init_data, int) M.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close>
    where type @{AllT_args} init_data = @{AllT_args} init_data
    where type @{AllT_args} data = int
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.M.t
  = \<^eval>\<open>sfx_T_nargs "Enumerable"\<close>(
  structure M = M
  type @{AllT_args} init_data = @{AllT_args} init_data
  type @{AllT_args} data = int
  val first = first
  fun next x = x |> M.arr (fn p => p + 1)
  fun prev x = x |> M.arr (fn p => p - 1)
)