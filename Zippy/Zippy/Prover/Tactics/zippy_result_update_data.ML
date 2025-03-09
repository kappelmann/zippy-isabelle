(*  Title:      HOCLP/zippy_result_update_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RESULT_UPDATE_DATA =
sig
  structure L : LENS
  type ('r, 'ud) result_update_data
  val result_update_data : ('p1, 'r * 'ud, ('r, 'ud) result_update_data) L.C.cat

  val result : unit -> ('p1, ('r, 'ud) result_update_data, 'r) L.slens
  val get_result : ('p1, ('r, 'ud) result_update_data, 'r) L.getter
  val map_result : ('p1, ('r, 'ud) result_update_data, 'r) L.smodifier

  val update_data : unit -> ('p1, ('r, 'ud) result_update_data, 'ud) L.slens
  val get_update_data : ('p1, ('r, 'ud) result_update_data, 'ud) L.getter
  val map_update_data : ('p1, ('r, 'ud) result_update_data, 'ud) L.smodifier
end

structure Zippy_Result_Update_Data :
    ZIPPY_RESULT_UPDATE_DATA
    where type ('p1, 'r, 'b) L.C.cat = ('p1, 'r, 'b) SLens.C.cat
    where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) SLens.lens
  =
struct

structure L = SLens

datatype ('r, 'ud) result_update_data = Result_Update_Data of {
    result : 'r,
    update_data : 'ud
  }

fun result_update_data (result, update_data) =
  Result_Update_Data {result = result, update_data = update_data}

fun get_result (Result_Update_Data {result,...}) = result
fun get_update_data (Result_Update_Data {update_data,...}) = update_data

fun map_result (f, (Result_Update_Data {result, update_data})) =
  Result_Update_Data {result = f result, update_data = update_data}
fun map_update_data (f, (Result_Update_Data {result, update_data})) =
  Result_Update_Data {result = result, update_data = f update_data}

fun result _ = L.lens get_result map_result
fun update_data _ = L.lens get_update_data map_update_data

end

signature KLEISLI_ZIPPY_RESULT_UPDATE_DATA =
sig
  structure K : KLEISLI
  include ZIPPY_RESULT_UPDATE_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_RESULT_UPDATE_DATA =
sig
  structure RUD : ZIPPY_RESULT_UPDATE_DATA
  include KLEISLI_ZIPPY_RESULT_UPDATE_DATA
  where type ('r, 'ud) result_update_data = ('r, 'ud) RUD.result_update_data
end

functor Lift_Zippy_Result_Update_Data(
    structure AF : ARROW
    structure RUD : ZIPPY_RESULT_UPDATE_DATA
    sharing type RUD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'r, 'b) C.cat = ('p1, 'r, 'b) AT.cat
    val lift : ('p1, 'r, 'b) AF.cat -> ('p1, 'r, 'b) AT.cat
  ) : LIFT_ZIPPY_RESULT_UPDATE_DATA =
struct

structure RUD = RUD
structure L = L
structure K = AT.K

type ('r, 'ud) result_update_data = ('r, 'ud) RUD.result_update_data

fun result_update_data x = x |> lift RUD.result_update_data
fun result_update_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (RUD.get_result, RUD.get_update_data))) result_update_data
fun result _ = L.lens_fst (result_update_data_lens ())
fun update_data _ = L.lens_snd (result_update_data_lens ())
fun get_result x = x |> L.get (result ())
fun map_result x = x |> L.modify (result ())
fun get_update_data x = x |> L.get (update_data ())
fun map_update_data x = x |> L.modify (update_data ())

end
