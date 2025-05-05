(*  Title:      Zippy/zippy_action_app_num_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN =
sig
  include ZIPPY_ACTION_APP_NUM_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  val inc_action_app_num : (@{ParaT_args} @{AllT_args} L.container) hom_move
end

functor Zippy_Action_App_Num_Mixin(
    ACTIONAN : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
  ) : ZIPPY_ACTION_APP_NUM_MIXIN =
struct

open ACTIONAN
structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(L.K.M); open M

fun inc_action_app_num x = L.modifier (arr ACTIONAN.inc_action_app_num, x)

end

