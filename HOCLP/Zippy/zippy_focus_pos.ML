(*  Title:      HOCLP/zippy_focus_pos.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_FOCUS_POS =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  datatype focus_pos = Single of GCS.goal_pos | List of GCS.goal_pos list | None
  val single : GCS.goal_pos -> focus_pos
  val list : GCS.goal_pos list -> focus_pos
  val none : focus_pos
end

functor Zippy_Focus_Pos(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_FOCUS_POS =
struct

structure GCS = GCS

datatype focus_pos = Single of GCS.goal_pos
  | List of GCS.goal_pos list
  | None

val single = Single
val list = List
val none = None

end