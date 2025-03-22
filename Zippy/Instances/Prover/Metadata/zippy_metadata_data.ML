(*  Title:      Zippy/zippy_metadata_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_METADATA_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('md, 'm) metadata_data
  val metadata_data : (@{ParaT_args} 'md * 'm, ('md, 'm) metadata_data) L.C.cat

  val metadata : unit -> (@{ParaT_args} ('md, 'm) metadata_data, 'md) L.slens
  val get_metadata : (@{ParaT_args} ('md, 'm) metadata_data, 'md) L.getter
  val map_metadata : (@{ParaT_args} ('md, 'm) metadata_data, 'md) L.smodifier

  val more : unit -> (@{ParaT_args} ('md, 'm) metadata_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('md, 'm) metadata_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('md, 'm) metadata_data, 'm) L.smodifier
end

structure Zippy_Metadata_Data :
  ZIPPY_METADATA_DATA
  where type (@{ParaT_args} 'md, 'b) L.C.cat =
    (@{ParaT_args} 'md, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

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
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_METADATA_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_METADATA_DATA =
sig
  structure MDD : ZIPPY_METADATA_DATA
  include KLEISLI_ZIPPY_METADATA_DATA
  where type ('md, 'm) metadata_data = ('md, 'm) MDD.metadata_data
end

functor Lift_Zippy_Metadata_Data(
    include LIFT_DATA_BASE
    structure MDD : ZIPPY_METADATA_DATA
    sharing type MDD.L.C.cat = AF.cat
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
