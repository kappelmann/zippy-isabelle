(*  Title:      Zippy/zippy_goal_clusters_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
  val get_gclusters_state : (@{ParaT_args} @{AllT_args} L.container, GCS.state) L.C.cat
  val is_gclusters_finished : (@{ParaT_args} @{AllT_args} L.container, bool) L.C.cat
end

functor Zippy_Goal_Clusters_Mixin(
    GClusters : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
  ) : ZIPPY_GOAL_CLUSTERS_MIXIN =
struct

open GClusters

fun get_gclusters_state x = x |> (L.getter #> GCS.get_state)
fun is_gclusters_finished x = x |> (L.getter #> GCS.is_finished)

end
