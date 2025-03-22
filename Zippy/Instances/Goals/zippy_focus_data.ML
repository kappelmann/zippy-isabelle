(*  Title:      HOCLP/zippy_focus_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_FOCUS_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('f, 'm) focus_data
  val focus_data : (@{ParaT_args} 'f * 'm, ('f, 'm) focus_data) L.C.cat

  val focus : unit -> (@{ParaT_args} ('f, 'm) focus_data, 'f) L.slens
  val get_focus : (@{ParaT_args} ('f, 'm) focus_data, 'f) L.getter
  val map_focus : (@{ParaT_args} ('f, 'm) focus_data, 'f) L.smodifier

  val more : unit -> (@{ParaT_args} ('f, 'm) focus_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('f, 'm) focus_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('f, 'm) focus_data, 'm) L.smodifier
end

structure Zippy_Focus_Data :
  ZIPPY_FOCUS_DATA
  where type (@{ParaT_args} 'f, 'b) L.C.cat =
    (@{ParaT_args} 'f, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

datatype ('f, 'm) focus_data = Focus_Data of {
    focus : 'f,
    more : 'm
  }

fun focus_data (focus, more) = Focus_Data {focus = focus, more = more}

fun get_focus (Focus_Data {focus,...}) = focus
fun get_more (Focus_Data {more,...}) = more

fun map_focus (f, (Focus_Data {focus, more})) = Focus_Data {focus = f focus, more = more}
fun map_more (f, (Focus_Data {focus, more})) = Focus_Data {focus = focus, more = f more}

fun focus _ = L.lens get_focus map_focus
fun more _ = L.lens get_more map_more

end

signature KLEISLI_ZIPPY_FOCUS_DATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_FOCUS_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_FOCUS_DATA =
sig
  structure FD : ZIPPY_FOCUS_DATA
  include KLEISLI_ZIPPY_FOCUS_DATA
  where type ('f, 'm) focus_data = ('f, 'm) FD.focus_data
end

functor Lift_Zippy_Focus_Data(
    include LIFT_DATA_BASE
    structure FD : ZIPPY_FOCUS_DATA
    sharing type FD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_FOCUS_DATA =
struct

structure FD = FD
structure L = L
structure K = AT.K

type ('f, 'm) focus_data = ('f, 'm) FD.focus_data

fun focus_data x = x |> lift FD.focus_data
fun focus_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (FD.get_focus, FD.get_more))) focus_data
fun focus _ = L.lens_fst (focus_data_lens ())
fun more _ = L.lens_snd (focus_data_lens ())
fun get_focus x = x |> L.get (focus ())
fun map_focus x = x |> L.modify (focus ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
