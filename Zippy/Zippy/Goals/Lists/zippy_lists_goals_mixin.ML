(*  Title:      Zippy/zippy_lists_goals_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_MIXIN =
sig
  include ZIPPY_GOALS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  (* lenses *)
  type @{AllT_args} node_gc
  (*sets goal clusters in order of cluster positions, i.e. [cpos 0, cpos 1,,..]*)
  val set_gcluster_list : (GCluster.GC.gcluster -> @{AllT_args} node_gc) ->
    GCluster.GC.gcluster list -> @{AllT_args} GClusters.L.container ->
    @{AllT_args} GClusters.L.container

  (* movements *)
  val move_cpos : GClusters.GCS.cluster_pos ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, @{AllT_args} GCluster.L.container) cat
end

functor Zippy_Lists_Goals_Mixin(
    structure Z : ZIPPY_LISTS
    structure Goals : ZIPPY_GOALS_MIXIN_BASE
    sharing type Goals.GClusters.L.container = Z.Z1.zipper
    sharing type Goals.GCluster.L.container = Z.Z2.zipper
  ) : ZIPPY_LISTS_GOALS_MIXIN =
struct

open Z Goals
structure MU = Zippy_Monad_Util(M); open MU
structure ZNU = Zippy_Node(structure Z = Z; structure AE = AE)

local open SC Mo
in
(* lenses *)
type @{AllT_args} node_gc = @{AllT_args} ZN.N2.node

fun set_gcluster_list mk_node gcs z = List.map mk_node gcs
  |> (fn c => L.set_modify ZNU.Node_Next1.modifier (pure c, z))

(* movements *)
fun move_cpos cpos = Down1.move >>> C.repeatn cpos Z2.ZM.Down.move
end

end