(*  Title:      Zippy/zippy_lists_goals_tactic_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  type @{AllT_args} node_gc
  val init_state : (@{ParaT_args} GClusters.GCS.gclusters, @{AllT_args} GClusters.L.container) cat ->
    (GCluster.GC.gcluster -> @{AllT_args} node_gc) -> (@{ParaT_args} GClusters.GCS.state,
      Tac.GPU.focus_update * @{AllT_args} GClusters.L.container) cat
end

functor Zippy_Lists_Goals_Tactic_Mixin(
    structure Z : ZIPPY_LISTS
    structure Goals_Tac : ZIPPY_GOALS_TACTIC_MIXIN_BASE
    sharing type Goals_Tac.GClusters.L.container = Z.Z1.zipper
    sharing type Goals_Tac.GCluster.L.container = Z.Z2.zipper
  ) : ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
struct

open Z Goals_Tac
structure MU = Zippy_Monad_Util(M); open MU
structure ZLG = Zippy_Lists_Goals_Mixin(structure Z = Z; structure Goals = Goals_Tac); open ZLG

local open Mo
in
fun init_state init_gcs mk_gc_node state =
  let
    val res = Tac.result () state Tac.GPU.id
    val (ud, (gcs, gc_list)) = Tac.init_result res
  in init_gcs gcs >>= arr (set_gcluster_list mk_gc_node gc_list #> pair ud) end
end

end
