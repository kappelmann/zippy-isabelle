(*  Title:      HOCLP/zippy_copy_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COPY_DATA =
sig
  structure L : LENS
  type ('c, 'm) copy_data
  val copy_data : ('p1, 'c * 'm, ('c, 'm) copy_data) L.C.cat

  val copy : unit -> ('p1, ('c, 'm) copy_data, 'c) L.slens
  val get_copy : ('p1, ('c, 'm) copy_data, 'c) L.getter
  val map_copy : ('p1, ('c, 'm) copy_data, 'c) L.smodifier

  val more : unit -> ('p1, ('c, 'm) copy_data, 'm) L.slens
  val get_more : ('p1, ('c, 'm) copy_data, 'm) L.getter
  val map_more : ('p1, ('c, 'm) copy_data, 'm) L.smodifier
end

structure Zippy_Copy_Data :
  ZIPPY_COPY_DATA where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('c, 'm) copy_data = Copy_Data of {
    copy : 'c,
    more : 'm
  }

fun copy_data (copy, more) =
  Copy_Data {copy = copy, more = more}

fun get_copy (Copy_Data {copy,...}) = copy
fun map_copy (f, (Copy_Data {copy, more})) = Copy_Data {copy = f copy, more = more}
fun copy _ = L.lens get_copy map_copy

fun get_more (Copy_Data {more,...}) = more
fun map_more (f, (Copy_Data {copy, more})) = Copy_Data {copy = copy, more = f more}
fun more _ = L.lens get_more map_more

end

signature LIFT_ZIPPY_COPY_DATA =
sig
  structure CD : ZIPPY_COPY_DATA
  include ZIPPY_COPY_DATA
  where type ('c, 'm) copy_data = ('c, 'm) CD.copy_data
end

functor Lift_Zippy_Copy_Data(
    structure AF : ARROW
    structure CD : ZIPPY_COPY_DATA
    sharing type CD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AT.cat
    val lift : ('p1, 'a, 'b) AF.cat -> ('p1, 'a, 'b) AT.cat
  ) : LIFT_ZIPPY_COPY_DATA =
struct

structure CD = CD
structure L = L

type ('cd, 'm) copy_data = ('cd, 'm) CD.copy_data

fun copy_data x = x |> lift CD.copy_data
fun copy_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (CD.get_copy, CD.get_more))) copy_data
fun copy _ = L.lens_fst (copy_data_lens ())
fun more _ = L.lens_snd (copy_data_lens ())
fun get_copy x = x |> L.get (copy ())
fun map_copy x = x |> L.modify (copy ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
