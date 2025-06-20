(*  Title:      Zippy/zippy_goal_cluster_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  val get_state : @{AllT_args} L.container -> GC.GCS.state
  val has_meta_vars : @{AllT_args} L.container -> bool
end

functor Zippy_Goal_Cluster_Mixin(
    GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  ) : ZIPPY_GOAL_CLUSTER_MIXIN =
struct

open GCluster

fun get_state x = x |> (L.getter #> GC.get_state)
fun has_meta_vars x = x |> (L.getter #> GC.has_meta_vars)

end
