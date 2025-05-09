(*  Title:      Zippy/zippy_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COPY_MIXIN =
sig
  include ZIPPY_COPY_MIXIN_BASE

  val get_run_copy : copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move

  val get_run_copy_safe : copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Copy_Mixin(
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
    sharing type AE.K.M.t = Copy.M.t
  ) : ZIPPY_COPY_MIXIN =
struct

open Copy

fun get_run_copy cud z3 z1 = L.getter z3 |> (run_copy #> (fn copy => copy cud z3 z1))
fun get_run_copy_safe cud z3 = AE.try (get_run_copy cud z3)

end

