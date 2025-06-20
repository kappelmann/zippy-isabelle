(*  Title:      Zippy/zippy_action_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_METADATA =
sig
  type description = string

  type metadata
  val metadata : Zippy_Identifier.id * description -> metadata

  val empty : Zippy_Identifier.id -> metadata

  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata -> Pretty.T

  structure Id : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = Zippy_Identifier.id

  structure Descr : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = description
end

structure Zippy_Action_Metadata : ZIPPY_ACTION_METADATA =
struct

structure Show = SpecCheck_Show_Base

type description = string

datatype metadata = Metadata of {
  id : Zippy_Identifier.id,
  description : description
}

fun metadata (id, description) = Metadata {id = id, description = description}
fun empty id = metadata (id, "")

fun eq_metadata (m1 as Metadata {id = id1, description = description1},
  m2 as Metadata {id = id2, description = description2}) =
  pointer_eq (m1, m2) orelse
  (Zippy_Identifier.eq_id (id1, id2) andalso description1 = description2)
fun pretty_metadata (Metadata {id, description}) = Show.record [
    ("id", Zippy_Identifier.pretty_id id),
    ("description", Show.string description)
  ]

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
structure Base = struct open L; type @{AllT_args} container = metadata end
structure Id =
struct
  open Base
  type @{AllT_args} data = Zippy_Identifier.id
  fun getter (Metadata {id,...}) = id
  fun modifier (f, (Metadata {id, description})) = Metadata {id = f id, description = description}
  fun lens _ = L.mk_lens getter modifier
end

structure Descr =
struct
  open Base
  type @{AllT_args} data = description
  fun getter (Metadata {description,...}) = description
  fun modifier (f, (Metadata {id, description})) = Metadata {id = id, description = f description}
  fun lens _ = L.mk_lens getter modifier
end

end
