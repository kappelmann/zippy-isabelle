(*  Title:      Zippy/zippy_lists_goals_tactic_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_MIXIN_BASE =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE
  type @{AllT_args} node_gc
end
