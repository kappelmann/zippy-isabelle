(*  Title:      HOCLP/zippy_focus.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_FOCUS =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  datatype focus = Goals of GCS.goal_pos list | None
  val goals : GCS.goal_pos list -> focus
  val single : GCS.goal_pos -> focus
  val none : focus
end

functor Zippy_Focus(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_FOCUS =
struct

structure GCS = GCS

datatype focus = Goals of GCS.goal_pos list | None

val goals = Goals
fun single x = Goals [x]
val none = None

end