(*  Title:      Zippy/zippy_runs_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUNS_MIXIN_BASE =
sig
  include ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
  structure PAction_Queue : ZIPPY_PACTION_QUEUE_MIXIN_BASE
  structure Action_App_Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
end

functor Zippy_Runs_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
    structure PAction_Queue : ZIPPY_PACTION_QUEUE_MIXIN_BASE
    structure Action_App_Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
  end) : ZIPPY_RUNS_MIXIN_BASE
  = A
