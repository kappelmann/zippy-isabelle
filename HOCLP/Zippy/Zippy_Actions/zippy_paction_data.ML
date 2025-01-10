(*  Title:      HOCLP/zippy_paction_data.ML
    Author:     Kevin Kappelmann

Data for actions with priorities.
*)
signature ZIPPY_PACTION_DATA =
sig
  structure L : LENS
  type ('pa, 'm) paction_data
  val paction_data : ('p1, 'pa * 'm, ('pa, 'm) paction_data) L.C.cat

  val paction : unit -> ('p1, ('pa, 'm) paction_data, 'pa) L.slens
  val get_paction : ('p1, ('pa, 'm) paction_data, 'pa) L.getter
  val map_paction : ('p1, ('pa, 'm) paction_data, 'pa) L.smodifier

  val more : unit -> ('p1, ('pa, 'm) paction_data, 'm) L.slens
  val get_more : ('p1, ('pa, 'm) paction_data, 'm) L.getter
  val map_more : ('p1, ('pa, 'm) paction_data, 'm) L.smodifier
end

structure Zippy_PAction_Data :
  ZIPPY_PACTION_DATA where type ('p1, 'pa, 'b) L.C.cat = ('p1, 'pa, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('pa, 'm) paction_data = PAction_Data of {
    paction : 'pa,
    more : 'm
  }

fun paction_data (paction, more) = PAction_Data {paction = paction, more = more}

fun get_paction (PAction_Data {paction,...}) = paction
fun get_more (PAction_Data {more,...}) = more

fun map_paction (f, (PAction_Data {paction, more})) = PAction_Data {paction = f paction, more = more}
fun map_more (f, (PAction_Data {paction, more})) = PAction_Data {paction = paction, more = f more}

fun paction _ = L.lens get_paction map_paction
fun more _ = L.lens get_more map_more

end

signature LIFT_ZIPPY_PACTION_DATA =
sig
  structure AD : ZIPPY_PACTION_DATA
  include ZIPPY_PACTION_DATA
  where type ('pa, 'm) paction_data = ('pa, 'm) AD.paction_data
end

functor Lift_Zippy_PAction_Data(
    structure AF : ARROW
    structure AD : ZIPPY_PACTION_DATA
    sharing type AD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'pa, 'b) C.cat = ('p1, 'pa, 'b) AT.cat
    val lift : ('p1, 'pa, 'b) AF.cat -> ('p1, 'pa, 'b) AT.cat
  ) : LIFT_ZIPPY_PACTION_DATA =
struct

structure AD = AD
structure L = L

type ('pa, 'm) paction_data = ('pa, 'm) AD.paction_data

fun paction_data x = x |> lift AD.paction_data
fun paction_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (AD.get_paction, AD.get_more))) paction_data
fun paction _ = L.lens_fst (paction_data_lens ())
fun more _ = L.lens_snd (paction_data_lens ())
fun get_paction x = x |> L.get (paction ())
fun map_paction x = x |> L.modify (paction ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end
