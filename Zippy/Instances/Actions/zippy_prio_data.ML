(*  Title:      HOCLP/zippy_prio_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRIO_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('p, 'm) prio_data
  val prio_data : (@{ParaT_args} 'p * 'm, ('p, 'm) prio_data) L.C.cat

  val prio : unit -> (@{ParaT_args} ('p, 'm) prio_data, 'p) L.slens
  val get_prio : (@{ParaT_args} ('p, 'm) prio_data, 'p) L.getter
  val map_prio : (@{ParaT_args} ('p, 'm) prio_data, 'p) L.smodifier

  val more : unit -> (@{ParaT_args} ('p, 'm) prio_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('p, 'm) prio_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('p, 'm) prio_data, 'm) L.smodifier
end

structure Zippy_Prio_Data :
  ZIPPY_PRIO_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat =
    (@{ParaT_args} 'a, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

datatype ('p, 'm) prio_data = Prio_Data of {
    prio : 'p,
    more : 'm
  }

fun prio_data (prio, more) = Prio_Data {prio = prio, more = more}

fun get_prio (Prio_Data {prio,...}) = prio
fun map_prio (f, (Prio_Data {prio, more})) = Prio_Data {prio = f prio, more = more}
fun prio _ = L.lens get_prio map_prio

fun get_more (Prio_Data {more,...}) = more
fun map_more (f, (Prio_Data {prio, more})) = Prio_Data {prio = prio, more = f more}
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_PRIO_DATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_PRIO_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_PRIO_DATA =
sig
  structure PD : ZIPPY_PRIO_DATA
  include KLEISLI_ZIPPY_PRIO_DATA
  where type ('p, 'm) prio_data = ('p, 'm) PD.prio_data
end

functor Lift_Zippy_Prio_Data(
    include LIFT_DATA_BASE
    structure PD : ZIPPY_PRIO_DATA
    sharing type PD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_PRIO_DATA =
struct

structure PD = PD
structure L = L
structure K = AT.K

type ('pd, 'm) prio_data = ('pd, 'm) PD.prio_data

fun prio_data x = x |> lift PD.prio_data
fun prio_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (PD.get_prio, PD.get_more))) prio_data
fun prio _ = L.lens_fst (prio_data_lens ())
fun more _ = L.lens_snd (prio_data_lens ())
fun get_prio x = x |> L.get (prio ())
fun map_prio x = x |> L.modify (prio ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
