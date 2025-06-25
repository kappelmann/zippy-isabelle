(*  Title:      Zippy/zippy_run_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RUN_MIXIN_BASE =
sig
  include ZIPPY_STEP_MIXIN_BASE
  structure Action_App_Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
end

functor Zippy_Run_Mixin_Base(A :
  sig
    include ZIPPY_STEP_MIXIN_BASE
    structure Action_App_Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
  end) : ZIPPY_RUN_MIXIN_BASE
  = A
