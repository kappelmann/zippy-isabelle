(*  Title:      Zippy/zippy_goals_tactic_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_MIXIN_BASE =
sig
  include ZIPPY_GOALS_MIXIN_BASE

  structure TAC : ZIPPY_ZTACTIC
  sharing type TAC.GPU.GCS.gcpos = GCS.GCS.gcpos
  sharing type TAC.GPU.GCS.gclusters = GCS.GCS.gclusters
  sharing type TAC.GC.gcluster = GC.GC.gcluster
end
