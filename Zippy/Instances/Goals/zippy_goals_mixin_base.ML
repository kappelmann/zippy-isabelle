(*  Title:      Zippy/zippy_goals_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_MIXIN_BASE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE

  structure GC : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  sharing type GC.L.K.M.t = GCS.L.K.M.t
  sharing type GC.L.lens = GCS.L.lens
  sharing type GC.GC.GCS.gcpos = GCS.GCS.gcpos
  sharing type GC.GC.GCS.gclusters = GCS.GCS.gclusters
end
