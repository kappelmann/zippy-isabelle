(*  Title:      HOCLP/zippy_result_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RESULT_METADATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>

  datatype progress = Promising | Unclear
  val promising : progress
  val unclear : progress
  val pretty_progress : progress -> Pretty.T

  type metadata
  val metadata : (@{ParaT_args} progress, metadata) L.C.cat

  val pretty_metadata : metadata -> Pretty.T

  val progress : unit -> (@{ParaT_args} metadata, progress) L.slens
  val get_progress : (@{ParaT_args} metadata, progress) L.getter
  val map_progress : (@{ParaT_args} metadata, progress) L.smodifier
end

structure Zippy_Result_Metadata :
  ZIPPY_RESULT_METADATA
  where type (@{ParaT_args} 'md, 'b) L.C.cat =
    (@{ParaT_args} 'md, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

datatype progress = Promising | Unclear

val promising = Promising
val unclear = Unclear

fun pretty_progress Promising = Pretty.str "Promising"
  | pretty_progress Unclear = Pretty.str "Unclear"

datatype metadata = Metadata of {
    progress : progress
  }
fun metadata progress = Metadata {progress = progress}

fun pretty_metadata (Metadata {progress}) = SpecCheck_Show_Base.record [
    ("progress", pretty_progress progress)
  ]

fun get_progress (Metadata {progress,...}) = progress
fun map_progress (f, (Metadata {progress})) = Metadata {progress = f progress}

fun progress _ = L.lens get_progress map_progress

end

signature KLEISLI_ZIPPY_RESULT_METADATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_RESULT_METADATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_RESULT_METADATA =
sig
  structure RMD : ZIPPY_RESULT_METADATA
  include KLEISLI_ZIPPY_RESULT_METADATA
  where type metadata = RMD.metadata
end

functor Lift_Zippy_Result_Metadata(
    include LIFT_DATA_BASE
    structure RMD : ZIPPY_RESULT_METADATA
    sharing type RMD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_RESULT_METADATA =
struct

structure RMD = RMD
structure Lin = L
open RMD
structure L = Lin
structure K = AT.K

type metadata = RMD.metadata

fun metadata x = x |> lift RMD.metadata
fun metadata_lens _ = L.lens_get_mk (lift RMD.get_progress) metadata
val progress = metadata_lens
fun get_progress x = x |> L.get (progress ())
fun map_progress x = x |> L.modify (progress ())

end
