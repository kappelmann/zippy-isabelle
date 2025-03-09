(*  Title:      HOCLP/zippy_focus_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_FOCUS_DATA =
sig
  structure L : LENS
  type ('f, 'm) focus_data
  val focus_data : ('p1, 'f * 'm, ('f, 'm) focus_data) L.C.cat

  val focus : unit -> ('p1, ('f, 'm) focus_data, 'f) L.slens
  val get_focus : ('p1, ('f, 'm) focus_data, 'f) L.getter
  val map_focus : ('p1, ('f, 'm) focus_data, 'f) L.smodifier

  val more : unit -> ('p1, ('f, 'm) focus_data, 'm) L.slens
  val get_more : ('p1, ('f, 'm) focus_data, 'm) L.getter
  val map_more : ('p1, ('f, 'm) focus_data, 'm) L.smodifier
end

structure Zippy_Focus_Data :
  ZIPPY_FOCUS_DATA where type ('p1, 'f, 'b) L.C.cat = ('p1, 'f, 'b) SLens.C.cat =
struct

structure L = SLens

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
  structure K : KLEISLI
  include ZIPPY_FOCUS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_FOCUS_DATA =
sig
  structure FD : ZIPPY_FOCUS_DATA
  include KLEISLI_ZIPPY_FOCUS_DATA
  where type ('f, 'm) focus_data = ('f, 'm) FD.focus_data
end

functor Lift_Zippy_Focus_Data(
    structure AF : ARROW
    structure FD : ZIPPY_FOCUS_DATA
    sharing type FD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'f, 'b) C.cat = ('p1, 'f, 'b) AT.cat
    val lift : ('p1, 'f, 'b) AF.cat -> ('p1, 'f, 'b) AT.cat
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
