(*  Title:      Zippy/zippy_action_cluster_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_CLUSTER_METADATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>

  type description = string

  type metadata
  val metadata : (@{ParaT_args} Zippy_Identifier.id * description, metadata) L.C.cat

  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata -> Pretty.T

  val id : unit -> (@{ParaT_args} metadata, Zippy_Identifier.id) L.slens
  val get_id : (@{ParaT_args} metadata, Zippy_Identifier.id) L.getter
  val map_id : (@{ParaT_args} metadata, Zippy_Identifier.id) L.smodifier

  val description : unit -> (@{ParaT_args} metadata, description) L.slens
  val get_description : (@{ParaT_args} metadata, description) L.getter
  val map_description : (@{ParaT_args} metadata, description) L.smodifier
end

structure Zippy_Action_Cluster_Metadata :
  ZIPPY_ACTION_CLUSTER_METADATA
  where type (@{ParaT_args} 'md, 'b) L.C.cat =
    (@{ParaT_args} 'md, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure Show = SpecCheck_Show_Base

type description = string

datatype metadata = Metadata of {
    id : Zippy_Identifier.id,
    description : description
  }
fun metadata (id, description) = Metadata {id = id, description = description}

fun eq_metadata (m1 as Metadata {id = id1, description = description1},
  m2 as Metadata {id = id2, description = description2}) =
  pointer_eq (m1, m2) orelse
  (Zippy_Identifier.eq_id (id1, id2) andalso description1 = description2)
fun pretty_metadata (Metadata {id, description}) = SpecCheck_Show_Base.record [
    ("id", Zippy_Identifier.pretty_id id),
    ("description", Show.string description)
  ]

fun get_id (Metadata {id,...}) = id
fun get_description (Metadata {description,...}) = description

fun map_id (f, (Metadata {id, description})) =
  Metadata {id = f id, description = description}
fun map_description (f, (Metadata {id, description})) =
  Metadata {id = id, description = f description}

fun id _ = L.lens get_id map_id
fun description _ = L.lens get_description map_description

end

signature KLEISLI_ZIPPY_ACTION_CLUSTER_METADATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_ACTION_CLUSTER_METADATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_ACTION_CLUSTER_METADATA =
sig
  structure ACMD : ZIPPY_ACTION_CLUSTER_METADATA
  include KLEISLI_ZIPPY_ACTION_CLUSTER_METADATA
  where type metadata = ACMD.metadata
end

functor Lift_Zippy_Action_Cluster_Metadata(
    include LIFT_DATA_BASE
    structure ACMD : ZIPPY_ACTION_CLUSTER_METADATA
    sharing type ACMD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_ACTION_CLUSTER_METADATA =
struct

structure ACMD = ACMD
structure Lin = L
open ACMD
structure L = Lin
structure K = AT.K

type metadata = ACMD.metadata

fun metadata x = x |> lift ACMD.metadata
fun metadata_lens _ =
  L.lens_get_mk (lift (AF.&&& (ACMD.get_id, ACMD.get_description))) metadata
fun id _ = L.lens_fst (metadata_lens ())
fun description _ = L.lens_snd (metadata_lens ())
fun get_id x = x |> L.get (id ())
fun map_id x = x |> L.modify (id ())
fun get_description x = x |> L.get (description ())
fun map_description x = x |> L.modify (description ())

end
