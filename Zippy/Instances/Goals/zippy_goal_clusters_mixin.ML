(*  Title:      Zippy/zippy_goal_clusters_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
  val get_gclusters_state : (@{ParaT_args} @{AllT_args} zipper, GCS.state) cat
  val is_gclusters_finished : (@{ParaT_args} @{AllT_args} zipper, bool) cat
end

functor Zippy_Goal_Clusters_Mixin(
    structure Z : ZIPPY_BASE
    structure GCS : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
    sharing type GCS.zipper = Z.Z1.zipper
    sharing type GCS.M.t = Z.M.t
    sharing type GCS.L.lens = Z.L.lens
  ) : ZIPPY_GOAL_CLUSTERS_MIXIN =
struct

open Z GCS

local open SC
in
fun get_gclusters_state x = x |> (L.getter >>> arr GCS.get_state)
fun is_gclusters_finished x = x |> (L.getter >>> arr GCS.is_finished)
end

end
