(*  Title:      Zippy/zippy_lists_goals_tactic_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>

  type @{AllT_args} node_gc
  val init_state :
    (@{ParaT_args} GClusters.GCS.gclusters, @{AllT_args} GClusters.L.container) morph ->
    (GCluster.GC.gcluster -> @{AllT_args} node_gc) -> (@{ParaT_args} GClusters.GCS.state,
      Tac.GPU.focus_update * @{AllT_args} GClusters.L.container) morph
end

functor Zippy_Lists_Goals_Tactic_Mixin(
    structure Z : ZIPPY_LISTS
    structure Goals_Tac : ZIPPY_GOALS_TACTIC_MIXIN_BASE
    sharing type Goals_Tac.GClusters.L.container = Z.Z1.zipper
    sharing type Goals_Tac.GCluster.L.container = Z.Z2.zipper
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
struct

open Z Goals_Tac Log
structure MU = Zippy_Monad_Util(M); open MU
structure ZLG = Zippy_Lists_Goals_Mixin(structure Z = Z; structure Goals = Goals_Tac); open ZLG

local open Mo A
in
fun init_state init_gcs mk_gc_node state = Ctxt.get_ctxt () >>= (fn ctxt =>
  let
    val res = Tac.result () state Tac.GPU.id
    val (ud, (gcs, gc_list)) = Tac.init_result res
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
        Pretty.block [Pretty.str "Initialised state ", Zippy_Thm_State.pretty ctxt state,
          Pretty.str "."],
        Pretty.block [Pretty.str "Resulting goal clusters: ",
          GClusters.GCS.pretty_gclusters ctxt gcs]
      ] |> Pretty.block0 |> Pretty.string_of)
  in init_gcs gcs >>= arr (set_gcluster_list mk_gc_node gc_list #> pair ud) end)
end

end
