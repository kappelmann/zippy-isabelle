(*  Title:      HOCLP/zippy_goal_cluster.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  type gcluster
  val get_pos : gcluster -> GCS.cluster_pos
  val get_state : gcluster -> Zippy_Thm_State.state
  val init : GCS.gclusters * int list -> gcluster list
  val init' : GCS.gclusters -> gcluster list
end

functor Zippy_Goal_Cluster(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_GOAL_CLUSTER =
struct

structure GCS = GCS
structure TS = Zippy_Thm_State

datatype gcluster = GCluster of {
    pos : GCS.cluster_pos,
    state : TS.state
  }
fun mk_gcluster pos state = GCluster {state = state, pos = pos}
fun get_pos (GCluster {pos,...}) = pos
fun get_state (GCluster {state,...}) = state

fun init x = x
  |>> GCS.get_cclusters
  |> (op ~~)
  |> map_index (fn (pos, (ccluster, n)) => TS.init ccluster |> TS.unmk_conj n |> mk_gcluster pos)

fun init' gcluster = gcluster
  |> `(GCS.get_clusters_goals #> map length)
  |> swap |> init

end
