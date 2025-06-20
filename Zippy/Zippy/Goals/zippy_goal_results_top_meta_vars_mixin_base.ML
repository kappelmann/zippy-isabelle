(*  Title:      Zippy/zippy_goal_results_top_meta_vars_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_RESULTS_TOP_META_VARS_MIXIN_BASE =
sig
  type @{AllT_args} zipper
  structure Top_Meta_Vars : ZIPPY_TOP_META_VARS_MIXIN_BASE
  sharing type Top_Meta_Vars.L.container = zipper
  structure Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
  sharing type Results.L.container = zipper
end

functor Zippy_Goal_Results_Top_Meta_Vars_Mixin_Base(A :
  sig
    structure Top_Meta_Vars : ZIPPY_TOP_META_VARS_MIXIN_BASE
    structure Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
    sharing type Results.L.container = Top_Meta_Vars.L.container
  end) : ZIPPY_GOAL_RESULTS_TOP_META_VARS_MIXIN_BASE
  =
struct
open A
type @{AllT_args} zipper = @{AllT_args} Results.L.container
end