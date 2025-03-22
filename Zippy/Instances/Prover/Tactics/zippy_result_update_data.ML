(*  Title:      HOCLP/zippy_result_update_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RESULT_UPDATE_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('r, 'ud) result_update_data
  val result_update_data : (@{ParaT_args} 'r * 'ud, ('r, 'ud) result_update_data) L.C.cat

  val result : unit -> (@{ParaT_args} ('r, 'ud) result_update_data, 'r) L.slens
  val get_result : (@{ParaT_args} ('r, 'ud) result_update_data, 'r) L.getter
  val map_result : (@{ParaT_args} ('r, 'ud) result_update_data, 'r) L.smodifier

  val update_data : unit -> (@{ParaT_args} ('r, 'ud) result_update_data, 'ud) L.slens
  val get_update_data : (@{ParaT_args} ('r, 'ud) result_update_data, 'ud) L.getter
  val map_update_data : (@{ParaT_args} ('r, 'ud) result_update_data, 'ud) L.smodifier
end

structure Zippy_Result_Update_Data :
    ZIPPY_RESULT_UPDATE_DATA
    where type (@{ParaT_args} 'r, 'b) L.C.cat =
      (@{ParaT_args} 'r, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close>
    where type (@{ParaT_args} 't, 'o, 's, 'i) L.lens =
      (@{ParaT_args} 't, 'o, 's, 'i) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".lens"\<close>
  =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

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
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_RESULT_UPDATE_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_RESULT_UPDATE_DATA =
sig
  structure RUD : ZIPPY_RESULT_UPDATE_DATA
  include KLEISLI_ZIPPY_RESULT_UPDATE_DATA
  where type ('r, 'ud) result_update_data = ('r, 'ud) RUD.result_update_data
end

functor Lift_Zippy_Result_Update_Data(
    include LIFT_DATA_BASE
    structure RUD : ZIPPY_RESULT_UPDATE_DATA
    sharing type RUD.L.C.cat = AF.cat
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
