(*  Title:      Zippy/zippy_lists_goals_tactic_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_TACTIC_COPY_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
  sharing type AE.K.M.t = M.t

  (* init result *)
  type @{AllT_args} node_gc
  val init_result :
    (GClusters.GCS.gclusters -> (@{ParaT_args} 'z5, @{AllT_args} GClusters.L.container) cat) ->
    (GCluster.GC.gcluster -> @{AllT_args} node_gc) -> 'm Tac.result ->
    (@{ParaT_args} 'z5, Copy.copy_update_data * @{AllT_args} GClusters.L.container) cat

  val init_result_copy_parents : (unit -> @{ParaT_args encl = "" ""} AE.exn) ->
    (GClusters.GCS.gclusters -> (@{ParaT_args} 'z5, @{AllT_args} GClusters.L.container) cat) ->
    (GCluster.GC.gcluster -> @{AllT_args} node_gc) -> 'm Tac.result ->
    (@{ParaT_args} 'z5, Copy.copy_update_data * @{AllT_args} Copy.zipper_to) cat
end

functor Zippy_Lists_Goals_Tactic_Copy_Mixin(
    structure Z : ZIPPY_LISTS
    structure GTC : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
    sharing type GTC.GClusters.L.container = Z.Z1.zipper
    sharing type GTC.GCluster.L.container = Z.Z2.zipper
    sharing type GTC.Copy.zipper_from = Z.Z3.zipper
    sharing type GTC.Copy.zipper_to = Z.Z1.zipper
    sharing type GTC.Copy.M.t = Z.M.t
  ) : ZIPPY_LISTS_GOALS_TACTIC_COPY_MIXIN =
struct

open Z GTC
structure MU = Zippy_Monad_Util(M); open MU
structure Base = struct structure Z = Z end
structure ZLG = Zippy_Lists_Goals_Mixin(open Base; structure Goals = GTC); open ZLG
structure ZE = Zippy_Base_Enum(open Base; structure Co = Co)
structure ZEC = Zippy_Enum_Copy_Mixin(structure Z = ZE structure Copy = Copy)

local open SC Mo
in
(* init result *)
fun init_result add_gcs mk_gc_node res =
  let val (ud, (gcs, gc_list)) = Tac.init_result res
  in add_gcs gcs >>> arr (set_gcluster_list mk_gc_node gc_list #> pair ud) end

fun init_result_copy_parents mk_exn add_gcs mk_gc_node res = init_result add_gcs mk_gc_node res
  >>> (fn (cud, z) => ZEC.copy_parents mk_exn cud z >>= arr (pair cud))
end

end

