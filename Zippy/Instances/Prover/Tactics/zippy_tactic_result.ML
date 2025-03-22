(*  Title:      HOCLP/zippy_tactic_result.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_RESULT =
sig
  structure RD : ZIPPY_RESULT_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat =
    (@{ParaT_args} 'a, 'b) \<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply" ^ ".cat"\<close>
  structure RUD : ZIPPY_RESULT_UPDATE_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) RD.L.C.cat
  structure GPU : ZIPPY_GPOS_UPDATE_UTIL
  structure GC : ZIPPY_GOAL_CLUSTER
  sharing type GC.GCS.gcpos = GPU.GCS.gcpos
  sharing type GC.GCS.gclusters = GPU.GCS.gclusters

  type 'm result_data = (GC.GCS.state, 'm) RD.result_data
  type update_data = GPU.GCS.goal_pos GPU.gpos_update
  type 'm result_update_data = ('m result_data, update_data) RUD.result_update_data

  val init_result_update_data : 'm result_update_data ->
    (GPU.F.focus -> (GPU.GCS.cluster_pos * GPU.F.focus) list) *
      (GPU.GCS.gclusters * GC.gcluster list)

  val single_goal_update_data : (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) ->
    GPU.GCS.goal_pos -> int -> update_data
  val single_goal_empty_target : (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target)
  val single_goal_moved_target : (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target)
end

functor Zippy_Tactic_Result(
    structure RD : ZIPPY_RESULT_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat =
      (@{ParaT_args} 'a, 'b) \<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply" ^ ".cat"\<close>
    structure RUD : ZIPPY_RESULT_UPDATE_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) RD.L.C.cat
    structure GPU : ZIPPY_GPOS_UPDATE_UTIL
    structure GC : ZIPPY_GOAL_CLUSTER
    sharing type GC.GCS.gcpos = GPU.GCS.gcpos
    sharing type GC.GCS.gclusters = GPU.GCS.gclusters
  ) : ZIPPY_TACTIC_RESULT =
struct

structure RD = RD
structure RUD = RUD
structure GPU = GPU
structure GC = GC
open GPU

type 'm result_data = (GCS.state, 'm) RD.result_data
type update_data = GCS.goal_pos gpos_update
type 'm result_update_data = ('m result_data, update_data) RUD.result_update_data

structure SArrow_Arrow_Apply = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close>

fun init_result_update_data rud =
  let
    val get_state = RUD.get_result #> RD.get_result
    val (state, gpu) = SArrow_Arrow_Apply.A.&&& (get_state, RUD.get_update_data) rud
    val res as (gclusters, gcluster_list) = GC.init_state state
  in
    gclusters_gcpos_update gclusters gpu
    |> update_focus (length gcluster_list)
    |> rpair res
  end

fun single_goal_update_data target_goal i nnew_goals j = if j < i
  then T.target [j]
  else if j = i then target_goal i nnew_goals
  else T.target [j + nnew_goals]

val single_goal_empty_target = K (K T.empty)
fun single_goal_moved_target i nnew_goals = T.target (i upto i + nnew_goals - 1)

end
