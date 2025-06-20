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

  (* finish *)
  (*TODO: remove/consolidate with other finish*)
  val finish_gclusters_fold :
    (@{ParaT_args} @{AllT_args} GCluster.L.container, @{AllT_args} GClusters.L.container list) cat ->
    ((@{ParaT_args} @{AllT_args} GClusters.L.container, thm Seq.seq) cat ->
      @{AllT_args} GClusters.L.container list -> (@{ParaT_args} thm Seq.seq) hom_move) ->
    Proof.context -> (@{ParaT_args} @{AllT_args} GClusters.L.container, thm Seq.seq) cat

  val finish_gclusters_oldest_first : Proof.context ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, thm Seq.seq) cat
  val finish_gclusters_newest_first : Proof.context ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, thm Seq.seq) cat
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
structure ZB = Zippy_Base(structure Z = Z; structure AE = AE)
structure ZG = Zippy_Goal_Cluster_Mixin(Goals.GCluster)
structure ZNU = Zippy_Node(structure Z = Z; structure AE = AE)

local open SC A Mo
in
(* lenses *)
type @{AllT_args} node_gc = @{AllT_args} ZN.N2.node

fun set_gcluster_list mk_node gcs z = List.map mk_node gcs
  |> (fn c => L.set_modify ZNU.Node_Next1.modifier (pure c, z))

(* movements *)
fun move_cpos cpos = Down1.move >>> C.repeatn cpos Z2.ZM.Down.move

(* finish *)
fun gen_finish_gclusters get_gcluster_list_statesq ctxt =
  AE.catch' get_gcluster_list_statesq (K Seq.empty) &&& arr GClusters.L.getter
  >>> arr (fn (gcluster_statesq, gcs) =>
    Seq.maps (fn gcluster_states => GClusters.GCS.finish_cluster_states ctxt gcluster_states gcs)
      gcluster_statesq
    (*base case: no more subgoals*)
    |> GClusters.GCS.is_finished gcs ? Seq.cons (GClusters.GCS.get_state gcs))
fun gen_get_gcluster_list_statesq finish_gcluster_list =
  Down1.move >>> list_container_zippers2 >>> finish_gcluster_list

local
  structure LTSM = \<^eval>\<open>sfx_ParaT_nargs "Traversable"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Seq_Monad_Trans"\<close>(M))))
in
fun gen_finish_gcluster_list finish_gcluster = LTSM.traverse finish_gcluster
end

fun seq_snoc sq x = Seq.append sq (Seq.single x)

fun gen_finish_gcluster list_gclusters_children fold_append finish_gclusters z =
  AE.catch' list_gclusters_children (K []) z
  >>= (fn gcs => fold_append finish_gclusters gcs Seq.empty)
  >>= arr (fn gcs_statesq => ZG.get_state z |> seq_snoc gcs_statesq)

(*tying the knot*)
fun finish_gclusters_fold list_gclusters_children fold_append ctxt x = x |>
  gen_finish_gclusters (get_gcluster_list_statesq_fold list_gclusters_children fold_append ctxt)
    ctxt
and get_gcluster_list_statesq_fold list_gclusters_children fold_append ctxt x = x |>
  gen_get_gcluster_list_statesq (finish_gcluster_list_fold list_gclusters_children fold_append ctxt)
and finish_gcluster_list_fold list_gclusters_children fold_append ctxt x = x |>
  gen_finish_gcluster_list (finish_gcluster_fold list_gclusters_children fold_append ctxt)
and finish_gcluster_fold list_gclusters_children fold_append ctxt x = x |>
  gen_finish_gcluster list_gclusters_children fold_append
    (finish_gclusters_fold list_gclusters_children fold_append ctxt)

fun list_zipper5_gclusters_children x = x |> (Down5.move >>> list_container_zippers1)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and list_zipper{i}_gclusters_children x = x |>
  (Down{i}.move
  >>> list_container_zippers\<^eval>\<open>succ_mod_nzippers {i}\<close>
  >>> ZB.LT.traverse
    (AE.catch' list_zipper\<^eval>\<open>succ_mod_nzippers {i}\<close>_gclusters_children (A.K []))
  >>> arr List.concat)\<close>
where start = 2 and stop = 4\<close>

local
  fun finish_gclusters x = finish_gclusters_fold list_zipper2_gclusters_children x
  fun apply_append f x acc = f x >>= arr (Seq.append acc)
  fun fold_newest_first_append f = fold_newest_first (apply_append f)
  fun fold_oldest_first_append f = fold_oldest_first (apply_append f)
in
fun finish_gclusters_oldest_first x = finish_gclusters fold_oldest_first_append x
fun finish_gclusters_newest_first x = finish_gclusters fold_newest_first_append x
end
end

end

