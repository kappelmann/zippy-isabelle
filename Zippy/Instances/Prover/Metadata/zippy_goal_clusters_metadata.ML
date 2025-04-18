(*  Title:      Zippy/zippy_goal_clusters_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS_METADATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>

  type metadata
  val metadata : (@{ParaT_args} bool, metadata) L.C.cat

  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata -> Pretty.T

  val is_result_returned : unit -> (@{ParaT_args} metadata, bool) L.slens
  val get_is_result_returned : (@{ParaT_args} metadata, bool) L.getter
  val map_is_result_returned : (@{ParaT_args} metadata, bool) L.smodifier
end

structure Zippy_Goal_Clusters_Metadata :
  ZIPPY_GOAL_CLUSTERS_METADATA
  where type (@{ParaT_args} 'md, 'b) L.C.cat =
    (@{ParaT_args} 'md, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure Show = SpecCheck_Show_Base

type description = string

datatype metadata = Metadata of {
    is_result_returned : bool
  }
fun metadata (is_result_returned) = Metadata {is_result_returned = is_result_returned}

fun eq_metadata (Metadata {is_result_returned = is_result_returned1},
  Metadata {is_result_returned = is_result_returned2}) =
  is_result_returned1 = is_result_returned2
fun pretty_metadata (Metadata {is_result_returned}) = SpecCheck_Show_Base.record [
    ("is_result_returned", Show.bool is_result_returned)
  ]

fun get_is_result_returned (Metadata {is_result_returned,...}) = is_result_returned

fun map_is_result_returned (f, (Metadata {is_result_returned})) =
  Metadata {is_result_returned = f is_result_returned}

fun is_result_returned _ = L.lens get_is_result_returned map_is_result_returned

end

signature KLEISLI_ZIPPY_GOAL_CLUSTERS_METADATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_GOAL_CLUSTERS_METADATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_GOAL_CLUSTERS_METADATA =
sig
  structure GCSMD : ZIPPY_GOAL_CLUSTERS_METADATA
  include KLEISLI_ZIPPY_GOAL_CLUSTERS_METADATA
  where type metadata = GCSMD.metadata
end

functor Lift_Zippy_Goal_Clusters_Metadata(
    include LIFT_DATA_BASE
    structure GCSMD : ZIPPY_GOAL_CLUSTERS_METADATA
    sharing type GCSMD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_GOAL_CLUSTERS_METADATA =
struct

structure GCSMD = GCSMD
structure Lin = L
open GCSMD
structure L = Lin
structure K = AT.K

type metadata = GCSMD.metadata

fun metadata x = x |> lift GCSMD.metadata
fun metadata_lens _ =
  L.lens_get_mk (lift GCSMD.get_is_result_returned) metadata
val is_result_returned = metadata_lens
fun get_is_result_returned x = x |> L.get (is_result_returned ())
fun map_is_result_returned x = x |> L.modify (is_result_returned ())

end
