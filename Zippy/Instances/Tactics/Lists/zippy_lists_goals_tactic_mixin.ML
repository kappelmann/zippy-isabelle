(*  Title:      Zippy/zippy_lists_goals_tactic_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
sig
  include ZIPPY_LISTS_GOALS_TACTIC_MIXIN_BASE

  (* lenses *)
  val set_gcluster_list : (@{ParaT_args} GC.GC.gcluster, @{AllT_args} node_gc) cat ->
    GC.GC.gcluster list -> (@{ParaT_args} @{AllT_args} GCS.zipper) hom_move

  (* movements *)
  val move_cpos : GCS.GCS.cluster_pos ->
    (@{ParaT_args} @{AllT_args} GCS.zipper, @{AllT_args} GC.zipper) cat

end

functor Zippy_Lists_Goals_Tactic_Mixin(
    structure Z : ZIPPY_LISTS_BASE
    structure GOALS_TAC : ZIPPY_LISTS_GOALS_TACTIC_MIXIN_BASE
    sharing type GOALS_TAC.GCS.zipper = Z.Z1.zipper
    sharing type GOALS_TAC.GC.zipper = Z.Z2.zipper
    sharing type GOALS_TAC.node_gc = Z.ZCORE.N2.node
    sharing type GOALS_TAC.M.t = Z.M.t
    sharing type GOALS_TAC.GCS.L.lens = Z.L.lens
  ) : ZIPPY_LISTS_GOALS_TACTIC_MIXIN =
struct

open Z GOALS_TAC
structure Z = Zippy_Base(structure Z = Z; structure CO = CO)
open Z

local open SC MO
in

(* lenses *)
fun set_gcluster_list mk_node gcs z = LT.traverse mk_node gcs
  >>= (fn n => set_safe NODE_NEXT1.modifier n z)

(* movements *)
fun move_cpos cpos = Down1.move >>> C.repeatn cpos next2

end

end

