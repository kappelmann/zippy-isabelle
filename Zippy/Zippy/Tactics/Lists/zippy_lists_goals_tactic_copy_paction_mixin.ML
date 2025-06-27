(*  Title:      Zippy/zippy_lists_goals_tactic_copy_paction_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_COPY_PACTION_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_PACTION_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = Copy.M.t
  structure Exn : ZIPPY_EXCEPTION_MIXIN_BASE
  sharing type Exn.M.t = M.t

  (* add actions *)
  val add_actions :
    ((@{ParaT_args} @{AllT_args} Copy.zipper_from, @{AllT_args} PAction.zipper) morph) list ->
    (@{ParaT_args} @{AllT_args} Copy.zipper_from) emorph

  (* add action clusters *)
  val add_action_clusters :
    ('a -> (@{ParaT_args} @{AllT_args} GCluster.L.container, @{AllT_args} Copy.zipper_from) morph) ->
    (GClusters.GCS.cluster_pos * 'a) list ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  type @{AllT_args} node_co
  val cons_action_cluster : @{ParaT_args encl = "(" ")"} Exn.ME.exn ->
    (*create node content*)
    (@{AllT_args} Copy.copy -> @{AllT_args} node_co) ->
    (*list of pairs of initial focus and actions to add*)
    (Tac.GPU.F.focus * (Tac.GPU.F.focus ->
      (@{ParaT_args} @{AllT_args} Copy.zipper_from, @{AllT_args} PAction.zipper) morph)) list ->
    (@{ParaT_args} @{AllT_args} GCluster.L.container, @{AllT_args} Copy.zipper_from) morph
end

functor Zippy_Lists_Goals_Tactic_Copy_PAction_Mixin(
    structure Z : ZIPPY_LISTS
    structure GTCP : ZIPPY_GOALS_TACTIC_COPY_PACTION_MIXIN_BASE
    sharing type GTCP.GClusters.L.container = Z.Z1.zipper
    sharing type GTCP.GCluster.L.container = Z.Z2.zipper
    sharing type GTCP.Copy.zipper_from = Z.Z3.zipper
    sharing type GTCP.Copy.zipper_to = Z.Z1.zipper
    sharing type GTCP.PAction.zipper = Z.Z4.zipper
    sharing type GTCP.Copy.M.t = Z.M.t
  ) : ZIPPY_LISTS_GOALS_TACTIC_COPY_PACTION_MIXIN =
struct

open Z GTCP
structure MU = Zippy_Monad_Util(M); open MU
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = Z; structure Goals = GTCP)
structure Exn = Zippy_Exception_Mixin(Z.Co)
structure ZB = Zippy_Base(structure Z = Z; structure Exn = Exn)
structure GTC = Zippy_Goals_Tactic_Copy_Mixin(GTCP)

local open SC Exn
in
(* add actions *)
fun add_actions add_actions =
  ZB.LF.foldlM (fn add_action => AE.try (add_action >>> Z.Up4.morph)) add_actions

(* add action clusters *)
fun add_action_clusters add_action_cluster = ZB.LF.foldlM
  (fn (cpos, x) => LGoals.move_cpos cpos
    >>> AE.try (add_action_cluster x >>> Up3.morph)
    >>> Up2.morph)

type @{AllT_args} node_co = @{AllT_args} ZN.N3.content
fun cons_action_cluster exn mk_node add_action_focus_list =
  let
    fun init_copy cud _ = GTC.focus_list_apply_copy_update_data cud add_action_focus_list
      |> add_action_clusters (cons_action_cluster exn mk_node)
    val copy = Copy.copy init_copy
    val add_actions = add_actions (List.map (fn (x, f) => f x) add_action_focus_list)
  in cons_content_move_safe2 exn (mk_node copy) >>> add_actions end
end
end
