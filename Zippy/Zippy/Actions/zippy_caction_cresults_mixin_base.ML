(*  Title:      Zippy/zippy_caction_cresults_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CACTION_CRESULTS_MIXIN_BASE =
sig
  type cost
  structure CAction : ZIPPY_CACTION_MIXIN_BASE
  sharing type CAction.cost = cost

  structure CResults : ZIPPY_CRESULTS_MIXIN_BASE
  sharing type CResults.M.t = CAction.M.t
  sharing type CResults.zipper = CAction.zipper
  sharing type CResults.cost = cost
end

functor Zippy_CAction_CResults_Mixin_Base(A :
  sig
    structure CAction : ZIPPY_CACTION_MIXIN_BASE
    structure CResults : ZIPPY_CRESULTS_MIXIN_BASE
    sharing type CResults.M.t = CAction.M.t
    sharing type CResults.zipper = CAction.zipper
    sharing type CResults.cost = CAction.cost
  end
  ) : ZIPPY_CACTION_CRESULTS_MIXIN_BASE
  =
struct
open A
type cost = CAction.cost
end