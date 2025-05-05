(*  Title:      Zippy/zippy_copy_mixin_base.ML
    Author:     Kevin Kappelmann

Copy mechanism.
*)
signature ZIPPY_COPY_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} copy
  type @{AllT_args} zipper_from
  type @{AllT_args} zipper_to

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type L.container = zipper_from
  sharing type L.data = copy
  sharing type L.K.M.t = M.t

  type copy_update_data

  val copy : (copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move) -> @{AllT_args} copy
  val run_copy : @{AllT_args} copy -> copy_update_data ->
    @{AllT_args} zipper_from -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end
