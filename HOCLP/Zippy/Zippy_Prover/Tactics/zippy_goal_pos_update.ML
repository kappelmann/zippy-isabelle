(*  Title:      HOCLP/zippy_goal_pos_update.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GPOS_UPDATE_TARGET =
sig
  datatype 't target = Skip | Move of 't
  val skip : 't target
  val move : 't -> 't target

  val map : ('t -> 'u) -> 't target -> 'u target
end

structure Zippy_GPos_Update_Target : ZIPPY_GPOS_UPDATE_TARGET =
struct
datatype 't target = Skip | Move of 't

val skip = Skip
fun move x = Move x

fun map _ Skip = skip
  | map f (Move t) = move (f t)
end

signature ZIPPY_GPOS_UPDATE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  structure T : ZIPPY_GPOS_UPDATE_TARGET
  type 't gpos_update = GCS.goal_pos -> 't T.target
  val id : GCS.goal_pos gpos_update
  val comp : 't gpos_update -> GCS.goal_pos gpos_update -> 't gpos_update
  val comp_pure : 't gpos_update -> (GCS.goal_pos -> GCS.goal_pos) -> 't gpos_update
  val pure_comp : (GCS.goal_pos -> 't) -> GCS.goal_pos gpos_update -> 't gpos_update

  val update : GCS.goal_pos -> 't T.target -> 't gpos_update -> 't gpos_update

  val gclusters_gcpos_update : GCS.gclusters -> GCS.goal_pos gpos_update -> GCS.gcpos gpos_update
end

functor Zippy_GPos_Update(
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure T : ZIPPY_GPOS_UPDATE_TARGET
  ) : ZIPPY_GPOS_UPDATE =
struct

structure GCS = GCS
structure T = T

type 't gpos_update = GCS.goal_pos -> 't T.target

val id = T.move

fun comp f g p = case g p of
    T.Skip => T.skip
  | T.Move p => f p
fun comp_pure f g = f o g
fun pure_comp f g p = g p |> T.map f

fun update p = General_Util.fun_update (equal p)

fun gclusters_gcpos_update gclusters = pure_comp (GCS.get_gcpos_index gclusters)

end
