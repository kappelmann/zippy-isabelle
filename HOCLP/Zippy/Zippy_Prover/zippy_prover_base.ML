(*  Title:      HOCLP/zippy_prover_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_BASE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  structure GC : ZIPPY_GOAL_CLUSTER
  sharing type GC.GCS.gclusters = GCS.gclusters
  sharing type GC.GCS.gcpos = GCS.gcpos
  structure F : ZIPPY_FOCUS
  sharing type F.GCS.gclusters = GCS.gclusters
  sharing type F.GCS.gcpos = GCS.gcpos

  include ZIPPY_WITH_GOALS
  where type gclusters = GCS.gclusters
  where type gcluster = GC.gcluster
  where type focus = F.focus
end

functor Zippy_Prover_Base(
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure GC : ZIPPY_GOAL_CLUSTER
    sharing type GC.GCS.gcpos = GCS.gcpos
    sharing type GC.GCS.gclusters = GCS.gclusters
    structure F : ZIPPY_FOCUS
    sharing type F.GCS.gcpos = GCS.gcpos
    sharing type F.GCS.gclusters = GCS.gclusters
    structure Z : ZIPPY_WITH_GOALS
    where type gclusters = GCS.gclusters
    where type gcluster = GC.gcluster
    where type focus = F.focus
  ) : ZIPPY_PROVER_BASE =
struct

structure GCS = GCS
structure GC = GC
structure F = F
open Z

end
