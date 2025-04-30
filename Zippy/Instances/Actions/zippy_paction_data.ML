(*  Title:      Zippy/zippy_paction_data.ML
    Author:     Kevin Kappelmann

Data for actions with priorities.
*)
signature ZIPPY_PACTION_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('pa, 'm) paction_data
  val paction_data : (@{ParaT_args} 'pa * 'm, ('pa, 'm) paction_data) L.C.cat

  val paction : unit -> (@{ParaT_args} ('pa, 'm) paction_data, 'pa) L.slens
  val get_paction : (@{ParaT_args} ('pa, 'm) paction_data, 'pa) L.getter
  val map_paction : (@{ParaT_args} ('pa, 'm) paction_data, 'pa) L.smodifier

  val more : unit -> (@{ParaT_args} ('pa, 'm) paction_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('pa, 'm) paction_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('pa, 'm) paction_data, 'm) L.smodifier
end

structure Zippy_PAction_Data :
  ZIPPY_PACTION_DATA
  where type (@{ParaT_args} 'pa, 'b) L.C.cat =
    (@{ParaT_args} 'pa, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

datatype ('pa, 'm) paction_data = PAction_Data of {
    paction : 'pa,
    more : 'm
  }

fun paction_data (paction, more) = PAction_Data {paction = paction, more = more}

fun get_paction (PAction_Data {paction,...}) = paction
fun get_more (PAction_Data {more,...}) = more

fun map_paction (f, (PAction_Data {paction, more})) = PAction_Data {paction = f paction, more = more}
fun map_more (f, (PAction_Data {paction, more})) = PAction_Data {paction = paction, more = f more}

fun paction _ = L.mk_lens get_paction map_paction
fun more _ = L.mk_lens get_more map_more

end

signature KLEISLI_ZIPPY_PACTION_DATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_PACTION_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_PACTION_DATA =
sig
  structure PAD : ZIPPY_PACTION_DATA
  include KLEISLI_ZIPPY_PACTION_DATA
  where type ('pa, 'm) paction_data = ('pa, 'm) PAD.paction_data
end

functor Lift_Zippy_PAction_Data(
    include \<^eval>\<open>sfx_ParaT_nargs "LIFT_DATA_BASE"\<close>
    structure PAD : ZIPPY_PACTION_DATA
    sharing type PAD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_PACTION_DATA =
struct

structure PAD = PAD
structure L = L
structure K = AT.K

type ('pa, 'm) paction_data = ('pa, 'm) PAD.paction_data

fun paction_data x = x |> lift PAD.paction_data
fun paction_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (PAD.get_paction, PAD.get_more))) paction_data
fun paction _ = L.lens_fst (paction_data_lens ())
fun more _ = L.lens_snd (paction_data_lens ())
fun get_paction x = x |> L.get (paction ())
fun map_paction x = x |> L.modify (paction ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
