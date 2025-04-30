(*  Title:      Zippy/zippy_goal_pos_update.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_POS_UPDATE_TARGET =
sig
  datatype 't target = Target of 't list
  val empty : 't target
  val target : 't list -> 't target
  val map_list : ('t list -> 'u list) -> 't target -> 'u target
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  where type (@{ParaT_args} 'a) t = 'a target
end

structure Zippy_Goal_Pos_Update_Target : ZIPPY_GOAL_POS_UPDATE_TARGET =
struct
datatype 't target = Target of 't list
val empty = Target []
fun target x = Target x
fun dest_target (Target t) = t

fun map_list f (Target t) = target (f t)

type (@{ParaT_args} 'a) t = 'a target
fun map f (Target t) = target (List.map f t)
fun pure x = Target [x]
fun bind (Target t) f = List.map (f #> dest_target) t |> flat |> target
fun f <*> x = bind f (fn f => map f x)
end

signature ZIPPY_GOAL_POS_UPDATE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  structure T : ZIPPY_GOAL_POS_UPDATE_TARGET
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
  where type (@{ParaT_args} 'a) K.M.t = (@{ParaT_args} 'a) T.t

  type 't gpos_update = (unit, GCS.goal_pos, 't) A.cat
  val id : GCS.goal_pos gpos_update
  val comp : 't gpos_update -> GCS.goal_pos gpos_update -> 't gpos_update
  val comp_pure : 't gpos_update -> (GCS.goal_pos -> GCS.goal_pos) -> 't gpos_update
  val pure_comp : (GCS.goal_pos -> 't) -> GCS.goal_pos gpos_update -> 't gpos_update

  val update : GCS.goal_pos -> 't T.target -> 't gpos_update -> 't gpos_update

  val gclusters_gcpos_update : GCS.gclusters -> GCS.goal_pos gpos_update ->
    GCS.gcpos gpos_update
end

functor Zippy_Goal_Pos_Update(
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure T : ZIPPY_GOAL_POS_UPDATE_TARGET
  ) : ZIPPY_GOAL_POS_UPDATE =
struct

structure GCS = GCS
structure T = T

type 't gpos_update = GCS.goal_pos -> 't T.target

structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(T)
val id = A.id ()

val comp = A.comp
fun comp_pure f g = f o g
fun pure_comp f g p = g p |> T.map f

fun update p = General_Util.fun_update (equal p)

fun gclusters_gcpos_update gclusters = pure_comp (GCS.get_gcpos_index gclusters)

end
