(*  Title:      Zippy/zippy_goal_focus.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_FOCUS =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  datatype focus = Goals of GCS.goal_pos list | None
  val goals : GCS.goal_pos list -> focus
  val single : GCS.goal_pos -> focus
  val none : focus
  val pretty : focus SpecCheck_Show.show

  val focused_data_none_each : focus -> 'a list -> (GCS.goal_pos * 'a) list
  val focused_data_none_no : focus -> 'a list -> (GCS.goal_pos * 'a) list
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

fun get_indices _ [] _ = []
  | get_indices i (j :: js) (x :: xs) = if i = j
      then (i, x) :: get_indices (i + 1) js xs
      else get_indices (i + 1) (j :: js) xs
  | get_indices i is _ = error (Pretty.breaks [
        Pretty.block [Pretty.str "Bad remaining arguments for get_indices."],
        Pretty.block [Pretty.str "Counter: ", SpecCheck_Show.int i],
        Pretty.block [Pretty.str "Indices: ", SpecCheck_Show.list SpecCheck_Show.int is]
      ] |> Pretty.block |> Pretty.string_of)

fun gen_focused_data fnone None = fnone
  | gen_focused_data _ (Goals gposs) = get_indices 1 gposs

fun focused_data_none_each x = gen_focused_data (tag_list 1) x
fun focused_data_none_no x = gen_focused_data (K []) x
end

structure Standard_Zippy_Goal_Focus = Zippy_Goal_Focus(Standard_Zippy_Goal_Clusters)