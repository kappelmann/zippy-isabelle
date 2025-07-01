(*  Title:      Zippy/zippy_ztactic_result.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ZTACTIC_RESULT_UTIL =
sig
  include ZIPPY_ZTACTIC_RESULT
  structure GC : ZIPPY_GOAL_CLUSTER
  sharing type GC.GCS.gcpos = GPU.GCS.gcpos
  sharing type GC.GCS.gclusters = GPU.GCS.gclusters

  val init_result : 'm result -> GPU.focus_update * (GPU.GCS.gclusters * GC.gcluster list)

  val single_goal_gpos_update : (int -> gpos_update) -> GPU.GCS.goal_pos -> int -> gpos_update
  val single_goal_empty_target : int -> gpos_update
  val single_goal_moved_target : int -> gpos_update
end

functor Zippy_ZTactic_Result_Util(A :
  sig
    include ZIPPY_ZTACTIC_RESULT
    structure GC : ZIPPY_GOAL_CLUSTER
    sharing type GC.GCS.gcpos = GPU.GCS.gcpos
    sharing type GC.GCS.gclusters = GPU.GCS.gclusters
  end
  ) : ZIPPY_ZTACTIC_RESULT_UTIL =
struct

open A

local open A.GPU
in
fun init_result {state, gpos_update,...} =
  let val goals as (gclusters, gcluster_list) =  GC.init_state state
  in
    gclusters_gcpos_update gclusters gpos_update
    |> update_focus (length gcluster_list)
    |> rpair goals
  end

fun single_goal_gpos_update update_goal i nnew_goals j = if j < i
  then T.target [j]
  else if j = i then update_goal nnew_goals i
  else T.target [j + nnew_goals]

val single_goal_empty_target = K (K T.empty)
fun single_goal_moved_target nnew_goals i = T.target (i upto i + nnew_goals - 1)
end

end

structure Standard_Zippy_ZTactic_Result_Util = Zippy_ZTactic_Result_Util(
  open Standard_ZTactic_Result; structure GC = Standard_Zippy_Goal_Cluster)
