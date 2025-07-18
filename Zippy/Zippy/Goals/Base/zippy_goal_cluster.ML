(*  Title:      Zippy/zippy_goal_cluster.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  type gcluster
  val get_pos : gcluster -> GCS.cluster_pos
  val get_state : gcluster -> GCS.state
  val get_thm : gcluster -> thm
  val get_ngoals : gcluster -> int
  val has_meta_vars : gcluster -> bool
  val meta_vars : gcluster -> Vars.set
  val pretty_gcluster : Proof.context -> gcluster SpecCheck_Show.show

  val init : GCS.gclusters * int list -> gcluster list
  val init' : GCS.gclusters -> gcluster list
  val init_state : GCS.state -> GCS.gclusters * gcluster list
end

functor Zippy_Goal_Cluster(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_GOAL_CLUSTER =
struct

structure GCS = GCS
structure TS = Zippy_Thm_State
structure GU = General_Util

datatype gcluster = GCluster of {
    pos : GCS.cluster_pos,
    state : TS.state,
    ngoals : int
  }
fun mk_gcluster pos state ngoals = GCluster {state = state, pos = pos, ngoals = ngoals}
fun get_pos (GCluster {pos,...}) = pos
fun get_state (GCluster {state,...}) = state
fun get_ngoals (GCluster {ngoals,...}) = ngoals
val get_thm = get_state #> TS.get_thm
val has_meta_vars = get_state #> TS.has_meta_vars
val meta_vars = get_state #> TS.meta_vars

fun pretty_gcluster ctxt = get_state #> Zippy_Thm_State.pretty ctxt

fun init x = x
  |>> GCS.get_cclusters
  |> (op ~~)
  |> map_index (fn (pos, (ccluster, n)) => TS.init ccluster |> TS.unmk_conj n
      |> (fn state => mk_gcluster pos state n))

fun init' gcluster = gcluster
  |> `(GCS.get_clusters_goals #> map length)
  |> swap |> init

fun init_state state =
  let val (gclusters, classes) = GCS.init state
  in (gclusters, init (gclusters, map snd classes)) end

end

structure Standard_Zippy_Goal_Cluster = Zippy_Goal_Cluster(Standard_Zippy_Goal_Clusters)