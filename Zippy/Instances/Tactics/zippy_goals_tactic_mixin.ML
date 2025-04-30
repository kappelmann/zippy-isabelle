(*  Title:      Zippy/zippy_goals_tactic_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE

  val gen_init_result : ('m TAC.result -> (@{ParaT_args} 'z4, 'z5) cat) ->
    (GCS.GCS.gclusters -> (@{ParaT_args} 'z5, 'z1) cat) ->
    (GC.GC.gcluster list -> (@{ParaT_args} 'z1, 'z2) cat) ->
    'm TAC.result -> (@{ParaT_args} 'z4,
      (TAC.GPU.F.focus -> (TAC.GPU.GCS.cluster_pos * TAC.GPU.F.focus) list) * 'z2) cat
end

functor Zippy_Goals_Tactic_Mixin(
    structure Z : ZIPPY_BASE
    structure GOALS_TAC : ZIPPY_GOALS_TACTIC_MIXIN_BASE
    sharing type GOALS_TAC.GCS.zipper = Z.Z1.zipper
    sharing type GOALS_TAC.GC.zipper = Z.Z2.zipper
    sharing type GOALS_TAC.M.t = Z.M.t
    sharing type GOALS_TAC.GCS.L.lens = Z.L.lens
  ) : ZIPPY_GOALS_TACTIC_MIXIN =
struct

open Z GOALS_TAC

local open SC MO A
in
(*TODO*)
(* fun presults_from_tac exn mk_prio_sq_c tac =
  GC.get_gcluster_state >>> arr tac >>> arr (presults_from_sq exn mk_prio_sq_c) *)

fun gen_init_result add_move_actiona_node set_gcs set_gc_list res =
  let val (ud, (gcs, gc_list)) = TAC.init_result res
  in add_move_actiona_node res >>> set_gcs gcs >>> set_gc_list gc_list >>> arr (pair ud) end

(*TODO*)
(* fun mk_result_actiona_node rddm prio rud =
  L.get (action_actiona_num ()) &&& L.get (action_focus ())
  >>> (fn (actiona_num, focus) =>
    mk_actiona_node rddm (T.RUD.get_result rud) focus actiona_num prio)
 *)
end

end

