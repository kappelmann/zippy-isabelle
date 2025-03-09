(*  Title:      HOCLP/zippy_metadata_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_METADATA_DATA =
sig
  structure L : LENS
  type ('md, 'm) metadata_data
  val metadata_data : ('p1, 'md * 'm, ('md, 'm) metadata_data) L.C.cat

  val metadata : unit -> ('p1, ('md, 'm) metadata_data, 'md) L.slens
  val get_metadata : ('p1, ('md, 'm) metadata_data, 'md) L.getter
  val map_metadata : ('p1, ('md, 'm) metadata_data, 'md) L.smodifier

  val more : unit -> ('p1, ('md, 'm) metadata_data, 'm) L.slens
  val get_more : ('p1, ('md, 'm) metadata_data, 'm) L.getter
  val map_more : ('p1, ('md, 'm) metadata_data, 'm) L.smodifier
end

structure Zippy_Metadata_Data :
  ZIPPY_METADATA_DATA where type ('p1, 'md, 'b) L.C.cat = ('p1, 'md, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('md, 'm) metadata_data = Metadata_Data of {
    metadata : 'md,
    more : 'm
  }

fun metadata_data (metadata, more) = Metadata_Data {metadata = metadata, more = more}

fun get_metadata (Metadata_Data {metadata,...}) = metadata
fun get_more (Metadata_Data {more,...}) = more

fun map_metadata (f, (Metadata_Data {metadata, more})) = Metadata_Data {metadata = f metadata, more = more}
fun map_more (f, (Metadata_Data {metadata, more})) = Metadata_Data {metadata = metadata, more = f more}

fun metadata _ = L.lens get_metadata map_metadata
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_METADATA_DATA =
sig
  structure K : KLEISLI
  include ZIPPY_METADATA_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_METADATA_DATA =
sig
  structure MDD : ZIPPY_METADATA_DATA
  include KLEISLI_ZIPPY_METADATA_DATA
  where type ('md, 'm) metadata_data = ('md, 'm) MDD.metadata_data
end

functor Lift_Zippy_Metadata_Data(
    structure AF : ARROW
    structure MDD : ZIPPY_METADATA_DATA
    sharing type MDD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'md, 'b) C.cat = ('p1, 'md, 'b) AT.cat
    val lift : ('p1, 'md, 'b) AF.cat -> ('p1, 'md, 'b) AT.cat
  ) : LIFT_ZIPPY_METADATA_DATA =
struct

structure MDD = MDD
structure L = L
structure K = AT.K

type ('md, 'm) metadata_data = ('md, 'm) MDD.metadata_data

fun metadata_data x = x |> lift MDD.metadata_data
fun metadata_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (MDD.get_metadata, MDD.get_more))) metadata_data
fun metadata _ = L.lens_fst (metadata_data_lens ())
fun more _ = L.lens_snd (metadata_data_lens ())
fun get_metadata x = x |> L.get (metadata ())
fun map_metadata x = x |> L.modify (metadata ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
