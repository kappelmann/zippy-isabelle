(*  Title:      Zippy/zippy_tactic_result_progress.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_RESULT_PROGRESS =
sig
  datatype progress = Promising | Unclear
  val promising : progress
  val unclear : progress
  val pretty : progress -> Pretty.T
end

structure Zippy_Tactic_Result_Progress : ZIPPY_TACTIC_RESULT_PROGRESS =
struct

datatype progress = Promising | Unclear

val promising = Promising
val unclear = Unclear

fun pretty Promising = Pretty.str "Promising"
  | pretty Unclear = Pretty.str "Unclear"

end