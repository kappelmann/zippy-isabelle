(*  Title:      Zippy/zippy_action_app_num_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN =
sig
  include ZIPPY_ACTION_APP_NUM_MIXIN_BASE

  val inc_action_app_num : (@{ParaT_args} @{AllT_args} zipper) hom_move
end

functor Zippy_Action_App_Num_Mixin(
    structure Z : ZIPPY_BASE
    structure ACTIONAN : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
    sharing type ACTIONAN.zipper = Z.Z4.zipper
    sharing type ACTIONAN.M.t = Z.M.t
    sharing type ACTIONAN.L.lens = Z.L.lens
  ) : ZIPPY_ACTION_APP_NUM_MIXIN =
struct

open Z ACTIONAN

fun inc_action_app_num x = L.modifier (arr ACTIONAN.inc_action_app_num, x)

end

