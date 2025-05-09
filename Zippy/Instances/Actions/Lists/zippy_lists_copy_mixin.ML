(*  Title:      Zippy/zippy_lists_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_COPY_MIXIN =
sig
  include ZIPPY_COPY_MIXIN_BASE
  val copy_parents : copy_update_data -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Lists_Copy_Mixin(
    structure Z : ZIPPY_LISTS
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    sharing type Copy.zipper_from = Z.Z3.zipper
    sharing type Copy.zipper_to = Z.Z1.zipper
    sharing type Copy.M.t = Z.M.t
  ) : ZIPPY_LISTS_COPY_MIXIN =
struct

open Z Copy
structure U = Zippy_Monad_Util(M); open U
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(ZCore_AZ2.L.M))
structure ZC = Zippy_Copy_Mixin(structure Copy = Copy; structure AE = AE)

local open SC Mo
in
fun copy_parents cud z =
  (Up1.move >>> Up5.move >>> Up4.move >>> list_container_zippers3) z
  >>= (fn zs => fold_oldest_first (ZC.get_run_copy_safe cud) zs z)
end

end

