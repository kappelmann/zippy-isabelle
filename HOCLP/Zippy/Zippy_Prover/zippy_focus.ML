(*  Title:      HOCLP/zippy_focus.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_FOCUS =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  datatype focus = Single of GCS.goal_pos | List of GCS.goal_pos list | None
  val single : GCS.goal_pos -> focus
  val list : GCS.goal_pos list -> focus
  val none : focus
end

functor Zippy_Focus(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_FOCUS =
struct

structure GCS = GCS

datatype focus = Single of GCS.goal_pos
  | List of GCS.goal_pos list
  | None

val single = Single
val list = List
val none = None

end