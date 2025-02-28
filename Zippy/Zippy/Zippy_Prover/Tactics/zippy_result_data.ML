(*  Title:      HOCLP/zippy_result_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RESULT_DATA =
sig
  structure L : LENS
  type ('r, 'm) result_data
  val result_data : ('p1, 'r * 'm, ('r, 'm) result_data) L.C.cat

  val result : unit -> ('p1, ('r, 'm) result_data, 'r) L.slens
  val get_result : ('p1, ('r, 'm) result_data, 'r) L.getter
  val map_result : ('p1, ('r, 'm) result_data, 'r) L.smodifier

  val more : unit -> ('p1, ('r, 'm) result_data, 'm) L.slens
  val get_more : ('p1, ('r, 'm) result_data, 'm) L.getter
  val map_more : ('p1, ('r, 'm) result_data, 'm) L.smodifier
end

structure Zippy_Result_Data :
  ZIPPY_RESULT_DATA where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('r, 'm) result_data = Result_Data of {
    result : 'r,
    more : 'm
  }

fun result_data (result, more) = Result_Data {result = result, more = more}

fun get_result (Result_Data {result,...}) = result
fun map_result (f, (Result_Data {result, more})) = Result_Data {result = f result, more = more}
fun result _ = L.lens get_result map_result

fun get_more (Result_Data {more,...}) = more
fun map_more (f, (Result_Data {result, more})) = Result_Data {result = result, more = f more}
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_RESULT_DATA =
sig
  structure K : KLEISLI
  include ZIPPY_RESULT_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_RESULT_DATA =
sig
  structure RD : ZIPPY_RESULT_DATA
  include KLEISLI_ZIPPY_RESULT_DATA
  where type ('r, 'm) result_data = ('r, 'm) RD.result_data
end

functor Lift_Zippy_result_Data(
    structure AF : ARROW
    structure RD : ZIPPY_RESULT_DATA
    sharing type RD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AT.cat
    val lift : ('p1, 'a, 'b) AF.cat -> ('p1, 'a, 'b) AT.cat
  ) : LIFT_ZIPPY_RESULT_DATA =
struct

structure RD = RD
structure L = L
structure K = AT.K

type ('r, 'm) result_data = ('r, 'm) RD.result_data

fun result_data x = x |> lift RD.result_data
fun result_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (RD.get_result, RD.get_more))) result_data
fun result _ = L.lens_fst (result_data_lens ())
fun more _ = L.lens_snd (result_data_lens ())
fun get_result x = x |> L.get (result ())
fun map_result x = x |> L.modify (result ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end

