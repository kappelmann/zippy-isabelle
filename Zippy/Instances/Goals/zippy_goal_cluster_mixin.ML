(*  Title:      Zippy/zippy_goal_cluster_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  val get_gcluster_state : (@{ParaT_args} @{AllT_args} L.container, GC.GCS.state) L.C.cat
end

functor Zippy_Goal_Cluster_Mixin(
    GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  ) : ZIPPY_GOAL_CLUSTER_MIXIN =
struct

open GCluster

fun get_gcluster_state x = x |> (L.getter #> GC.get_state)

end
