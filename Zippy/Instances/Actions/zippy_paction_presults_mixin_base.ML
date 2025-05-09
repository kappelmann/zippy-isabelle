(*  Title:      Zippy/zippy_paction_presults_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_PRESULTS_MIXIN_BASE =
sig
  structure PAction : ZIPPY_PACTION_MIXIN_BASE

  structure PResults : ZIPPY_PRESULTS_MIXIN_BASE
  where type (@{ParaT_args} 'a, 'b) Co.C.cat = (@{ParaT_args} 'a, 'b) PAction.cat
  sharing type PResults.zipper = PAction.zipper
  sharing type PResults.prio = PAction.prio
end
