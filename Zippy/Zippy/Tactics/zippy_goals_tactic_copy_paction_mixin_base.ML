(*  Title:      Zippy/zippy_goals_tactic_copy_paction_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_PACTION_MIXIN_BASE =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE

  structure PAction : ZIPPY_PACTION_MIXIN
  sharing type PAction.M.t = Copy.M.t
end

functor Zippy_Goals_Tactic_Copy_PAction_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
    structure PAction : ZIPPY_PACTION_MIXIN
    sharing type PAction.M.t = Copy.M.t
  end) : ZIPPY_GOALS_TACTIC_COPY_PACTION_MIXIN_BASE
  = A

