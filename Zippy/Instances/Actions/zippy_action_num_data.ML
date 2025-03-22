(*  Title:      Zippy/zippy_actiona_num_data.ML
    Author:     Kevin Kappelmann

Action application number.
*)
signature ZIPPY_ACTIONA_NUM_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('an, 'm) actiona_num_data
  val actiona_num_data : (@{ParaT_args} 'an * 'm, ('an, 'm) actiona_num_data) L.C.cat

  val actiona_num : unit -> (@{ParaT_args} ('an, 'm) actiona_num_data, 'an) L.slens
  val get_actiona_num : (@{ParaT_args} ('an, 'm) actiona_num_data, 'an) L.getter
  val map_actiona_num : (@{ParaT_args} ('an, 'm) actiona_num_data, 'an) L.smodifier

  val more : unit -> (@{ParaT_args} ('an, 'm) actiona_num_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('an, 'm) actiona_num_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('an, 'm) actiona_num_data, 'm) L.smodifier
end

structure Zippy_Actiona_Num_Data :
  ZIPPY_ACTIONA_NUM_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat =
    (@{ParaT_args} 'a, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

datatype ('an, 'm) actiona_num_data = Actiona_Num_Data of {
    actiona_num : 'an,
    more : 'm
  }

fun actiona_num_data (actiona_num, more) =
  Actiona_Num_Data {actiona_num = actiona_num, more = more}

fun get_actiona_num (Actiona_Num_Data {actiona_num,...}) = actiona_num
fun map_actiona_num (f, (Actiona_Num_Data {actiona_num, more})) =
  Actiona_Num_Data {actiona_num = f actiona_num, more = more}
fun actiona_num _ = L.lens get_actiona_num map_actiona_num

fun get_more (Actiona_Num_Data {more,...}) = more
fun map_more (f, (Actiona_Num_Data {actiona_num,more})) =
  Actiona_Num_Data {actiona_num = actiona_num, more = f more}
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_ACTIONA_NUM_DATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_ACTIONA_NUM_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_ACTIONA_NUM_DATA =
sig
  structure AND : ZIPPY_ACTIONA_NUM_DATA
  include KLEISLI_ZIPPY_ACTIONA_NUM_DATA
  where type ('an, 'm) actiona_num_data = ('an, 'm) AND.actiona_num_data
end

functor Lift_Zippy_Actiona_Num_Data(
    include LIFT_DATA_BASE
    structure AND : ZIPPY_ACTIONA_NUM_DATA
    sharing type AND.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_ACTIONA_NUM_DATA =
struct

structure AND = AND
structure L = L
structure K = AT.K

type ('an, 'm) actiona_num_data = ('an, 'm) AND.actiona_num_data

fun actiona_num_data x = x |> lift AND.actiona_num_data
fun actiona_num_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (AND.get_actiona_num, AND.get_more)))
    actiona_num_data
fun actiona_num _ = L.lens_fst (actiona_num_data_lens ())
fun get_actiona_num x = x |> L.get (actiona_num ())
fun map_actiona_num x = x |> L.modify (actiona_num ())
fun more _ = L.lens_snd (actiona_num_data_lens ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end

