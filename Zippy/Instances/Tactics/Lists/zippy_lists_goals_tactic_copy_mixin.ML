(*  Title:      Zippy/zippy_lists_goals_tactic_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_COPY_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} node_gc

  val copy_cpos_focus :
    (TAC.GPU.F.focus -> @{AllT_args} COPY.zipper_from ->
      (@{ParaT_args} @{AllT_args} GC.L.container, @{AllT_args} GCS.L.container) cat) ->
    (GCS.GCS.cluster_pos * TAC.GPU.F.focus) -> @{AllT_args} COPY.zipper_from ->
    (@{ParaT_args} @{AllT_args} GCS.L.container) hom_move

  val copy_cpos_focus_list :
    (TAC.GPU.F.focus -> @{AllT_args} COPY.zipper_from ->
      (@{ParaT_args} @{AllT_args} GC.L.container, @{AllT_args} GCS.L.container) cat) ->
    (GCS.GCS.cluster_pos * TAC.GPU.F.focus) list -> @{AllT_args} COPY.zipper_from ->
    (@{ParaT_args} @{AllT_args} GCS.L.container) hom_move

  val copy_update_focus :
    (TAC.GPU.F.focus -> @{AllT_args} COPY.zipper_from ->
      (@{ParaT_args} @{AllT_args} GC.L.container, @{AllT_args} GCS.L.container) cat) ->
    TAC.GPU.F.focus -> @{AllT_args} COPY.copy

  val init_result_copy_parents :
    (GCS.GCS.gclusters -> (@{ParaT_args} 'z5, @{AllT_args} GCS.L.container) cat) ->
    (@{ParaT_args} GC.GC.gcluster, @{AllT_args} node_gc) cat ->
    'm TAC.result -> (@{ParaT_args} 'z5, @{AllT_args} COPY.zipper_to) cat
end

functor Zippy_Lists_Goals_Tactic_Copy_Mixin(
    structure Z : ZIPPY_LISTS
    structure GOALS_TAC_COPY : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
    sharing type GOALS_TAC_COPY.GCS.L.container = Z.Z1.zipper
    sharing type GOALS_TAC_COPY.GC.L.container = Z.Z2.zipper
    sharing type GOALS_TAC_COPY.COPY.zipper_from = Z.Z3.zipper
    sharing type GOALS_TAC_COPY.COPY.zipper_to = Z.Z1.zipper
    sharing type GOALS_TAC_COPY.GCS.L.K.M.t = Z.M.t
    sharing type GOALS_TAC_COPY.GCS.L.lens = Z.L.lens
  ) : ZIPPY_LISTS_GOALS_TACTIC_COPY_MIXIN =
struct

open Z GOALS_TAC_COPY
structure U = Zippy_Monad_Util(M); open U
structure Base = struct structure Z = Z end
structure ZLGT = Zippy_Lists_Goals_Tactic_Mixin(open Base; structure GOALS_TAC = GOALS_TAC_COPY)
open ZLGT
structure ZGT = Zippy_Goals_Tactic_Mixin(GOALS_TAC_COPY)
structure ZLC = Zippy_Lists_Copy_Mixin(open Base; structure COPY = COPY)

local
  structure ZGTC = Zippy_Goals_Tactic_Copy_Mixin(
    structure AE = AE; structure GOALS_TAC_COPY = GOALS_TAC_COPY)
  open ZGTC
in
fun copy_cpos_focus init_copy = gen_copy_cpos_focus move_cpos init_copy
fun copy_cpos_focus_list init_copy = gen_copy_cpos_focus_list (copy_cpos_focus init_copy)
fun copy_update_focus init_copy = gen_copy_update_focus (copy_cpos_focus_list init_copy)
end

local open SC MO
in
fun init_result_copy_parents set_gcs mk_gc_node res =
  ZGT.gen_init_result set_gcs (set_gcluster_list mk_gc_node) res
  >>> uncurry ZLC.copy_parents
end


end

