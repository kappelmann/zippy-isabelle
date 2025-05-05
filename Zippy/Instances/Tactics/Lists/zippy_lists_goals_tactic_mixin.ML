(*  Title:      Zippy/zippy_lists_goals_tactic_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} node_gc

  (* lenses *)
  val set_gcluster_list : (@{ParaT_args} GC.GC.gcluster, @{AllT_args} node_gc) cat ->
    GC.GC.gcluster list -> (@{ParaT_args} @{AllT_args} GCS.L.container) hom_move

  (* movements *)
  val move_cpos : GCS.GCS.cluster_pos ->
    (@{ParaT_args} @{AllT_args} GCS.L.container, @{AllT_args} GC.L.container) cat

  val init_state :
    (@{ParaT_args} GCS.GCS.gclusters, @{AllT_args} GCS.L.container) cat ->
    (@{ParaT_args} GC.GC.gcluster, @{AllT_args} node_gc) cat ->
    (@{ParaT_args} GCS.GCS.state,
      (TAC.GPU.F.focus -> (GCS.GCS.cluster_pos * TAC.GPU.F.focus) list) *
      @{AllT_args} GCS.L.container) cat
end

functor Zippy_Lists_Goals_Tactic_Mixin(
    structure Z : ZIPPY_LISTS
    structure GOALS_TAC : ZIPPY_GOALS_TACTIC_MIXIN_BASE
    sharing type GOALS_TAC.GCS.L.container = Z.Z1.zipper
    sharing type GOALS_TAC.GC.L.container = Z.Z2.zipper
    sharing type GOALS_TAC.GCS.L.K.M.t = Z.M.t
    sharing type GOALS_TAC.GCS.L.lens = Z.L.lens
  ) : ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
struct

open Z GOALS_TAC
structure U = Zippy_Monad_Util(M); open U
structure ZB = Zippy_Base(structure Z = Z; structure AE = AE); open ZB
structure ZN = Zippy_Node(structure Z = Z; structure AE = AE); open ZN
structure ZGT = Zippy_Goals_Tactic_Mixin(GOALS_TAC)

type @{AllT_args} node_gc = @{AllT_args} ZCORE.N2.node

local open SC MO
in
(* lenses *)
fun set_gcluster_list mk_node gcs z = LT.traverse mk_node gcs
  >>= (fn n => set_safe NODE_NEXT1.modifier n z)

(* movements *)
fun move_cpos cpos = Down1.move >>> C.repeatn cpos next2

fun init_state set_gcs mk_gc_node state =
  let val res = TAC.result () state TAC.GPU.id
  in ZGT.gen_init_result (fn gcs => fn _ => set_gcs gcs) (set_gcluster_list mk_gc_node) res () end
end

end
