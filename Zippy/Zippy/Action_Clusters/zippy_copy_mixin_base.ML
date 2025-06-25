(*  Title:      Zippy/zippy_copy_mixin_base.ML
    Author:     Kevin Kappelmann

Copy mechanism.
*)
signature ZIPPY_COPY_MIXIN_BASE =
sig
  include HAS_LOGGER
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  type @{AllT_args} copy
  type @{AllT_args} zipper_from
  type @{AllT_args} zipper_to

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper_from
  sharing type L.data = copy

  type copy_update_data

  val copy : (copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move) -> @{AllT_args} copy
  val run_copy : @{AllT_args} copy -> copy_update_data ->
    @{AllT_args} zipper_from -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Copy_Mixin_Base(A :
  sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val parent_logger : Logger.logger_binding
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    type @{AllT_args} zipper_to
    type copy_update_data
    val copy : (copy_update_data -> @{AllT_args} L.container ->
      (@{ParaT_args} @{AllT_args} zipper_to) M.hom_move) -> @{AllT_args} L.data
    val run_copy : @{AllT_args} L.data -> copy_update_data ->
      @{AllT_args} L.container -> (@{ParaT_args} @{AllT_args} zipper_to) M.hom_move
  end
  ) : ZIPPY_COPY_MIXIN_BASE
  =
struct

open A A.M
structure FIU = Functor_Instance_Util(FIA)
val logger = Logger.setup_new_logger A.parent_logger FIU.base_name
val _ = @{print} logger

type @{AllT_args} zipper_from = @{AllT_args} L.container
type @{AllT_args} copy = @{AllT_args} L.data

end
