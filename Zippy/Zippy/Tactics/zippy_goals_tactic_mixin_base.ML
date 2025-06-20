(*  Title:      Zippy/zippy_goals_tactic_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_MIXIN_BASE =
sig
  include ZIPPY_GOALS_MIXIN_BASE

  structure Tac : ZIPPY_ZTACTIC
  sharing type Tac.GPU.GCS.gcpos = GClusters.GCS.gcpos
  sharing type Tac.GPU.GCS.gclusters = GClusters.GCS.gclusters
  sharing type Tac.GC.gcluster = GCluster.GC.gcluster
end

functor Zippy_Goals_Tactic_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_MIXIN_BASE
    structure Tac : ZIPPY_ZTACTIC
    sharing type Tac.GPU.GCS.gcpos = GClusters.GCS.gcpos
    sharing type Tac.GPU.GCS.gclusters = GClusters.GCS.gclusters
    sharing type Tac.GC.gcluster = GCluster.GC.gcluster
  end) : ZIPPY_GOALS_TACTIC_MIXIN_BASE
  = A