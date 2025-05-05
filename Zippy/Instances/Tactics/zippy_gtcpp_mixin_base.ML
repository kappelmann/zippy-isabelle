(*  Title:      Zippy/zippy_gtcpp_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GTCPP_MIXIN_BASE =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE

  include ZIPPY_PACTION_PRESULTS_MIXIN_BASE
  sharing type PACTION.M.t = GCS.L.K.M.t
  sharing type PACTION.L.lens = GCS.L.lens
end
