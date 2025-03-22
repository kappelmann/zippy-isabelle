(*  Title:      HOCLP/zippy_presults_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('pr, 'm) presults_data
  val presults_data : (@{ParaT_args} 'pr * 'm, ('pr, 'm) presults_data) L.C.cat

  val presults : unit -> (@{ParaT_args} ('pr, 'm) presults_data, 'pr) L.slens
  val get_presults : (@{ParaT_args} ('pr, 'm) presults_data, 'pr) L.getter
  val map_presults : (@{ParaT_args} ('pr, 'm) presults_data, 'pr) L.smodifier

  val more : unit -> (@{ParaT_args} ('pr, 'm) presults_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('pr, 'm) presults_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('pr, 'm) presults_data, 'm) L.smodifier
end

structure Zippy_PResults_Data :
  ZIPPY_PRESULTS_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat =
    (@{ParaT_args} 'a, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

datatype ('pr, 'm) presults_data = PResults_Data of {
    presults : 'pr,
    more : 'm
  }

fun presults_data (presults, more) =
  PResults_Data {presults = presults, more = more}

fun get_presults (PResults_Data {presults,...}) = presults
fun map_presults (f, (PResults_Data {presults, more})) =
  PResults_Data {presults = f presults, more = more}
fun presults _ = L.lens get_presults map_presults

fun get_more (PResults_Data {more,...}) = more
fun map_more (f, (PResults_Data {presults,more})) =
  PResults_Data {presults = presults, more = f more}
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_PRESULTS_DATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_PRESULTS_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_PRESULTS_DATA =
sig
  structure PRD : ZIPPY_PRESULTS_DATA
  include KLEISLI_ZIPPY_PRESULTS_DATA
  where type ('pr, 'm) presults_data = ('pr, 'm) PRD.presults_data
end

functor Lift_Zippy_PResults_Data(
    include LIFT_DATA_BASE
    structure PRD : ZIPPY_PRESULTS_DATA
    sharing type PRD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_PRESULTS_DATA =
struct

structure PRD = PRD
structure L = L
structure K = AT.K

type ('pr, 'm) presults_data = ('pr, 'm) PRD.presults_data

fun presults_data x = x |> lift PRD.presults_data
fun presults_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (PRD.get_presults, PRD.get_more)))
    presults_data
fun presults _ = L.lens_fst (presults_data_lens ())
fun get_presults x = x |> L.get (presults ())
fun map_presults x = x |> L.modify (presults ())
fun more _ = L.lens_snd (presults_data_lens ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
