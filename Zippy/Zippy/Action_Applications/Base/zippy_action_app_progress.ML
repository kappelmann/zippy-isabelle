(*  Title:      Zippy/zippy_action_app_progress.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_APP_PROGRESS =
sig
  datatype progress = Promising | Unclear
  val promising : progress
  val unclear : progress
  val pretty : progress -> Pretty.T
end

structure Zippy_Action_App_Progress : ZIPPY_ACTION_APP_PROGRESS =
struct

datatype progress = Promising | Unclear

val promising = Promising
val unclear = Unclear

fun pretty Promising = Pretty.str "Promising"
  | pretty Unclear = Pretty.str "Unclear"

end