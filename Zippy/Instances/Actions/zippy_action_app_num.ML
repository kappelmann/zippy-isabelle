(*  Title:      Zippy/zippy_action_app_num.ML
    Author:     Kevin Kappelmann

Action application numbers.
*)
signature ZIPPY_ACTION_APP_NUM =
sig
  type action_app_num = int
  val init_action_app_num : action_app_num
  val inc_action_app_num : action_app_num -> action_app_num
  val pretty : action_app_num -> Pretty.T
end

structure Zippy_Action_App_Num : ZIPPY_ACTION_APP_NUM =
struct
type action_app_num = int

val init_action_app_num = 0
fun inc_action_app_num x = x + 1

val pretty = SpecCheck_Show_Base.int
end
