(*  Title:      HOCLP/zippy_tactic_result.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_RESULT =
sig
  structure RD : ZIPPY_RESULT_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SArrow_Apply.cat
  structure RUD : ZIPPY_RESULT_UPDATE_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) RD.L.C.cat
  structure GPU : ZIPPY_GPOS_UPDATE_UTIL
  structure GC : ZIPPY_GOAL_CLUSTER
  sharing type GC.GCS.gcpos = GPU.GCS.gcpos
  sharing type GC.GCS.gclusters = GPU.GCS.gclusters

  type 'm result_data = (GC.GCS.state, 'm) RD.result_data
  type update_data = GPU.GCS.goal_pos GPU.gpos_update
  type 'm result_update_data = ('m result_data, update_data) RUD.result_update_data

  val init_result_update_data : 'm result_update_data ->
    (GPU.F.focus -> (GPU.GCS.cluster_pos * GPU.F.focus) list) * (GPU.GCS.gclusters * GC.gcluster list)

  val mk_single_goal_update_data : GPU.GCS.goal_pos -> int -> update_data
end

functor Zippy_Tactic_Result(
    structure RD : ZIPPY_RESULT_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SArrow_Apply.cat
    structure RUD : ZIPPY_RESULT_UPDATE_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) RD.L.C.cat
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

type 'm result_data = (GC.GCS.state, 'm) RD.result_data
type update_data = GPU.GCS.goal_pos GPU.gpos_update
type 'm result_update_data = ('m result_data, update_data) RUD.result_update_data

fun init_result_update_data rud =
  let
    val get_state = RUD.get_result #> RD.get_result
    val (state, gpu) = SArrow_Arrow_Apply.A.&&& (get_state, RUD.get_update_data) rud
    val res as (gclusters, gcluster_list) = GC.init_state state
  in
    GPU.gclusters_gcpos_update gclusters gpu
    |> GPU.update_focus (length gcluster_list)
    |> rpair res
  end

fun mk_single_goal_update_data i nnew_goals j =
  if j < i then GPU.T.Move j else if j = i then GPU.T.Skip else GPU.T.Move (j + nnew_goals)

end
