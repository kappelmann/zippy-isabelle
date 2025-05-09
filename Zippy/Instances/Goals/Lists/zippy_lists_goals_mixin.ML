(*  Title:      Zippy/zippy_lists_goals_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_MIXIN =
sig
  include ZIPPY_GOALS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  (* finish *)
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
structure U = Zippy_Monad_Util(M); open U
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(open Z Co.AE)
structure ZB = Zippy_Base(structure Z = Z; structure AE = AE)
structure ZG = Zippy_Goal_Cluster_Mixin(Goals.GCluster)

local open SC A Mo
in
(* finish *)
local
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

fun gen_finish_gcluster list_gclusters_children fold_append finish_gclusters z =
  AE.catch' list_gclusters_children (K []) z
  >>= (fn gcs => fold_append finish_gclusters gcs Seq.empty)
  >>= arr (fn gcs_statesq => ZG.get_gcluster_state z |> ZB.seq_snoc gcs_statesq)
in
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
end

fun list_zipper5_gclusters_children x = x |> (Down5.move >>> list_container_zippers1)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and list_zipper{i}_gclusters_children x = x |>
  (Down{i}.move
  >>> list_container_zippers\<^eval>\<open>succ_mod_nzippers {i}\<close>
  >>> LT.traverse (AE.catch' list_zipper\<^eval>\<open>succ_mod_nzippers {i}\<close>_gclusters_children (K []))
  >>> arr List.concat)\<close>
where start = 2 and stop = 4\<close>

local
fun apply_append f x acc = f x >>= arr (Seq.append acc)
fun fold_newest_first_append f = fold_newest_first (apply_append f)
fun fold_oldest_first_append f = fold_oldest_first (apply_append f)
fun finish_gclusters x = finish_gclusters_fold list_zipper2_gclusters_children x
in
fun finish_gclusters_oldest_first x = finish_gclusters fold_oldest_first_append x
fun finish_gclusters_newest_first x = finish_gclusters fold_newest_first_append x
end

end

end

