(*  Title:      HOCLP/zippy_action_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_METADATA =
sig
  structure L : LENS

  type description = string

  type metadata
  val metadata : ('p1, Zippy_Identifier.id * description, metadata) L.C.cat

  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata -> Pretty.T

  val id : unit -> ('p1, metadata, Zippy_Identifier.id) L.slens
  val get_id : ('p1, metadata, Zippy_Identifier.id) L.getter
  val map_id : ('p1, metadata, Zippy_Identifier.id) L.smodifier

  val description : unit -> ('p1, metadata, description) L.slens
  val get_description : ('p1, metadata, description) L.getter
  val map_description : ('p1, metadata, description) L.smodifier
end

structure Zippy_Action_Metadata :
  ZIPPY_ACTION_METADATA where type ('p1, 'md, 'b) L.C.cat = ('p1, 'md, 'b) SLens.C.cat =
struct

structure L = SLens
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

signature KLEISLI_ZIPPY_ACTION_METADATA =
sig
  structure K : KLEISLI
  include ZIPPY_ACTION_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_ACTION_METADATA =
sig
  structure AMD : ZIPPY_ACTION_METADATA
  include KLEISLI_ZIPPY_ACTION_METADATA
  where type metadata = AMD.metadata
end

functor Lift_Zippy_Action_Metadata(
    structure AF : ARROW
    structure AMD : ZIPPY_ACTION_METADATA
    sharing type AMD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'md, 'b) C.cat = ('p1, 'md, 'b) AT.cat
    val lift : ('p1, 'md, 'b) AF.cat -> ('p1, 'md, 'b) AT.cat
  ) : LIFT_ZIPPY_ACTION_METADATA =
struct

structure AMD = AMD
structure Lin = L
open AMD
structure L = Lin
structure K = AT.K

type metadata = AMD.metadata

fun metadata x = x |> lift AMD.metadata
fun metadata_lens _ =
  L.lens_get_mk (lift (AF.&&& (AMD.get_id, AMD.get_description))) metadata
fun id _ = L.lens_fst (metadata_lens ())
fun description _ = L.lens_snd (metadata_lens ())
fun get_id x = x |> L.get (id ())
fun map_id x = x |> L.modify (id ())
fun get_description x = x |> L.get (description ())
fun map_description x = x |> L.modify (description ())

end
