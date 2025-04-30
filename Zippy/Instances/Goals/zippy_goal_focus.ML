(*  Title:      Zippy/zippy_focus.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_FOCUS =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  datatype focus = Goals of GCS.goal_pos list | None
  val goals : GCS.goal_pos list -> focus
  val single : GCS.goal_pos -> focus
  val none : focus
  val pretty : focus -> Pretty.T
end

functor Zippy_Goal_Focus(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_GOAL_FOCUS =
struct
structure Show = SpecCheck_Show_Base

structure GCS = GCS

datatype focus = Goals of GCS.goal_pos list | None

val goals = Goals
fun single x = Goals [x]
val none = None
fun pretty (Goals xs) = Pretty.block [Pretty.str "Goals ", Pretty.block [Show.list Show.int xs]]
  | pretty None = Pretty.str "None"

end