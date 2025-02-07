(*  Title:      HOCLP/zippy_gclusters_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GCLUSTERS_DATA =
sig
  structure L : LENS
  type ('g, 'm) gclusters_data
  val gclusters_data : ('p1, 'g * 'm, ('g, 'm) gclusters_data) L.C.cat

  val gclusters : unit -> ('p1, ('g, 'm) gclusters_data, 'g) L.slens
  val get_gclusters : ('p1, ('g, 'm) gclusters_data, 'g) L.getter
  val map_gclusters : ('p1, ('g, 'm) gclusters_data, 'g) L.smodifier

  val more : unit -> ('p1, ('g, 'm) gclusters_data, 'm) L.slens
  val get_more : ('p1, ('g, 'm) gclusters_data, 'm) L.getter
  val map_more : ('p1, ('g, 'm) gclusters_data, 'm) L.smodifier
end

structure Zippy_GClusters_Data :
  ZIPPY_GCLUSTERS_DATA where type ('p1, 'g, 'b) L.C.cat = ('p1, 'g, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('g, 'm) gclusters_data = GClusters_Data of {
    gclusters : 'g,
    more : 'm
  }

fun gclusters_data (gclusters, more) = GClusters_Data {gclusters = gclusters, more = more}

fun get_gclusters (GClusters_Data {gclusters,...}) = gclusters
fun get_more (GClusters_Data {more,...}) = more

fun map_gclusters (f, (GClusters_Data {gclusters, more})) = GClusters_Data {gclusters = f gclusters, more = more}
fun map_more (f, (GClusters_Data {gclusters, more})) = GClusters_Data {gclusters = gclusters, more = f more}

fun gclusters _ = L.lens get_gclusters map_gclusters
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_GCLUSTERS_DATA =
sig
  structure K : KLEISLI
  include ZIPPY_GCLUSTERS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_GCLUSTERS_DATA =
sig
  structure GCSD : ZIPPY_GCLUSTERS_DATA
  include KLEISLI_ZIPPY_GCLUSTERS_DATA
  where type ('g, 'm) gclusters_data = ('g, 'm) GCSD.gclusters_data
end

functor Lift_Zippy_GClusters_Data(
    structure AF : ARROW
    structure GCSD : ZIPPY_GCLUSTERS_DATA
    sharing type GCSD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'g, 'b) C.cat = ('p1, 'g, 'b) AT.cat
    val lift : ('p1, 'g, 'b) AF.cat -> ('p1, 'g, 'b) AT.cat
  ) : LIFT_ZIPPY_GCLUSTERS_DATA =
struct

structure GCSD = GCSD
structure L = L
structure K = AT.K

type ('g, 'm) gclusters_data = ('g, 'm) GCSD.gclusters_data

fun gclusters_data x = x |> lift GCSD.gclusters_data
fun gclusters_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (GCSD.get_gclusters, GCSD.get_more))) gclusters_data
fun gclusters _ = L.lens_fst (gclusters_data_lens ())
fun more _ = L.lens_snd (gclusters_data_lens ())
fun get_gclusters x = x |> L.get (gclusters ())
fun map_gclusters x = x |> L.modify (gclusters ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end

