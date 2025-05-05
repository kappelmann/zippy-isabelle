(*  Title:      Zippy/zippy_goals_tactic_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  val gen_init_result : (GCS.GCS.gclusters -> (@{ParaT_args} 'z5, 'z1) cat) ->
    (GC.GC.gcluster list -> (@{ParaT_args} 'z1, 'z2) cat) ->
    'm TAC.result -> (@{ParaT_args} 'z5,
      (TAC.GPU.F.focus -> (GCS.GCS.cluster_pos * TAC.GPU.F.focus) list) * 'z2) cat
end

functor Zippy_Goals_Tactic_Mixin(
    GOALS_TAC : ZIPPY_GOALS_TACTIC_MIXIN_BASE
  ) : ZIPPY_GOALS_TACTIC_MIXIN =
struct

open GOALS_TAC
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(GCS.L.K.M); open MB

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(MB); open SC
in
(*TODO*)
(* fun presults_from_tac exn mk_prio_sq_c tac =
  GC.get_gcluster_state >>> arr tac >>> arr (presults_from_sq exn mk_prio_sq_c) *)

fun gen_init_result set_gcs set_gc_list res =
  let val (ud, (gcs, gc_list)) = TAC.init_result res
  in set_gcs gcs >>> set_gc_list gc_list >>> arr (pair ud) end

(*TODO*)
(* fun mk_result_actiona_node rddm prio rud =
  L.get (action_actiona_num ()) &&& L.get (action_focus ())
  >>> (fn (actiona_num, focus) =>
    mk_actiona_node rddm (T.RUD.get_result rud) focus actiona_num prio)
 *)
end

end

