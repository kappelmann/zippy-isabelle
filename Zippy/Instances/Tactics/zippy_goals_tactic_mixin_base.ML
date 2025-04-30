(*  Title:      Zippy/zippy_goals_tactic_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  structure GCS : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
  sharing type GCS.M.t = M.t

  structure GC : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  sharing type GC.M.t = M.t
  sharing type GC.L.lens = GCS.L.lens
  sharing type GC.GC.GCS.gcpos = GCS.GCS.gcpos
  sharing type GC.GC.GCS.gclusters = GCS.GCS.gclusters

  structure TAC : ZIPPY_ZTACTIC
  sharing type TAC.GPU.GCS.gcpos = GCS.GCS.gcpos
  sharing type TAC.GPU.GCS.gclusters = GCS.GCS.gclusters
  sharing type TAC.GC.gcluster = GC.GC.gcluster
end
