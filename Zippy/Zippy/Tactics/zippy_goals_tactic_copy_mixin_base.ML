(*  Title:      Zippy/zippy_goals_tactic_copy_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE

  structure Copy : ZIPPY_COPY_MIXIN
  where type copy_update_data = Tac.GPU.focus_update
end

functor Zippy_Goals_Tactic_Copy_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_TACTIC_MIXIN_BASE
    structure Copy : ZIPPY_COPY_MIXIN
    where type copy_update_data = Tac.GPU.focus_update
  end) : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
  = A
