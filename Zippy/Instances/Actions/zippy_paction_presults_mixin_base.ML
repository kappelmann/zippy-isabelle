(*  Title:      Zippy/zippy_paction_presults_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN_BASE =
sig
  structure PACTION : ZIPPY_PACTION_MIXIN_BASE

  structure PRESULTS : ZIPPY_PRESULTS_MIXIN_BASE
  sharing type PRESULTS.zipper = PACTION.zipper
  sharing type PRESULTS.L.K.M.t = PACTION.M.t
  sharing type PRESULTS.prio = PACTION.prio
  sharing type PRESULTS.L.lens = PACTION.L.lens
end
