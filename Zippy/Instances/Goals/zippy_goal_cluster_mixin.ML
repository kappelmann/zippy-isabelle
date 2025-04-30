(*  Title:      Zippy/zippy_goal_cluster_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTER_MIXIN_BASE

  val get_gcluster_state : (@{ParaT_args} @{AllT_args} zipper, GC.GCS.state) cat
end

functor Zippy_Goal_Cluster_Mixin(
    structure Z : ZIPPY_BASE
    structure GC : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
    sharing type GC.zipper = Z.Z2.zipper
    sharing type GC.M.t = Z.M.t
    sharing type GC.L.lens = Z.L.lens
  ) : ZIPPY_GOAL_CLUSTER_MIXIN =
struct

open Z GC

local open SC
in
fun get_gcluster_state x = x |> (L.getter >>> arr GC.get_state)
end

end
