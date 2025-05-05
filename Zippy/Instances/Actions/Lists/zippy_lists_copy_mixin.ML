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
    structure COPY : ZIPPY_COPY_MIXIN_BASE
    sharing type COPY.zipper_from = Z.Z3.zipper
    sharing type COPY.zipper_to = Z.Z1.zipper
    sharing type COPY.M.t = Z.M.t
    sharing type COPY.L.lens = Z.L.lens
  ) : ZIPPY_LISTS_COPY_MIXIN =
struct

open Z COPY
structure U = Zippy_Monad_Util(M); open U
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(ZCOREAZ2.LI.M))
structure ZC = Zippy_Copy_Mixin(structure COPY = COPY; structure AE = AE); open ZC

local open SC MO
in
fun copy_parents cud z =
  (Up1.move >>> Up5.move >>> Up4.move >>> list_container_zippers3) z
  >>= (fn zs => fold_oldest_first (get_run_copy_safe cud) zs z)
end

end

