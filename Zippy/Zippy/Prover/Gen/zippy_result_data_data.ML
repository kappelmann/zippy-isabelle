(*  Title:      HOCLP/zippy_result_data_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RESULT_DATA_DATA =
sig
  structure L : LENS
  type ('rd, 'm) result_data_data
  val result_data_data : ('p1, 'rd * 'm, ('rd, 'm) result_data_data) L.C.cat

  val result_data : unit -> ('p1, ('rd, 'm) result_data_data, 'rd) L.slens
  val get_result_data : ('p1, ('rd, 'm) result_data_data, 'rd) L.getter
  val map_result_data : ('p1, ('rd, 'm) result_data_data, 'rd) L.smodifier

  val more : unit -> ('p1, ('rd, 'm) result_data_data, 'm) L.slens
  val get_more : ('p1, ('rd, 'm) result_data_data, 'm) L.getter
  val map_more : ('p1, ('rd, 'm) result_data_data, 'm) L.smodifier
end

structure Zippy_Result_Data_Data :
  ZIPPY_RESULT_DATA_DATA where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('rd, 'm) result_data_data = Result_Data_Data of {
  result_data : 'rd,
  more : 'm
}

fun result_data_data (result_data, more) = Result_Data_Data {result_data = result_data, more = more}

fun get_result_data (Result_Data_Data {result_data,...}) = result_data
fun map_result_data (f, (Result_Data_Data {result_data, more})) =
  Result_Data_Data {result_data = f result_data, more = more}
fun result_data _ = L.lens get_result_data map_result_data

fun get_more (Result_Data_Data {more,...}) = more
fun map_more (f, (Result_Data_Data {result_data, more})) =
  Result_Data_Data {result_data = result_data, more = f more}
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_RESULT_DATA_DATA =
sig
  structure K : KLEISLI
  include ZIPPY_RESULT_DATA_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_RESULT_DATA_DATA =
sig
  structure RDD : ZIPPY_RESULT_DATA_DATA
  include KLEISLI_ZIPPY_RESULT_DATA_DATA
  where type ('rd, 'm) result_data_data = ('rd, 'm) RDD.result_data_data
end

functor Lift_Zippy_Result_Data_Data(
    structure AF : ARROW
    structure RDD : ZIPPY_RESULT_DATA_DATA
    sharing type RDD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AT.cat
    val lift : ('p1, 'a, 'b) AF.cat -> ('p1, 'a, 'b) AT.cat
  ) : LIFT_ZIPPY_RESULT_DATA_DATA =
struct

structure RDD = RDD
structure L = L
structure K = AT.K

type ('rd, 'm) result_data_data = ('rd, 'm) RDD.result_data_data

fun result_data_data x = x |> lift RDD.result_data_data
fun result_data_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (RDD.get_result_data, RDD.get_more))) result_data_data
fun result_data _ = L.lens_fst (result_data_data_lens ())
fun more _ = L.lens_snd (result_data_data_lens ())
fun get_result_data x = x |> L.get (result_data ())
fun map_result_data x = x |> L.modify (result_data ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end

