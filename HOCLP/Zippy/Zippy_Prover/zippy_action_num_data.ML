(*  Title:      HOCLP/zippy_action_num_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_NUM_DATA =
sig
  structure L : LENS
  type ('an, 'm) action_num_data
  val action_num_data : ('p1, 'an * 'm, ('an, 'm) action_num_data) L.C.cat

  val action_num : unit -> ('p1, ('an, 'm) action_num_data, 'an) L.slens
  val get_action_num : ('p1, ('an, 'm) action_num_data, 'an) L.getter
  val map_action_num : ('p1, ('an, 'm) action_num_data, 'an) L.smodifier

  val more : unit -> ('p1, ('an, 'm) action_num_data, 'm) L.slens
  val get_more : ('p1, ('an, 'm) action_num_data, 'm) L.getter
  val map_more : ('p1, ('an, 'm) action_num_data, 'm) L.smodifier
end

structure Zippy_Action_Num_Data :
  ZIPPY_ACTION_NUM_DATA where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('an, 'm) action_num_data = Action_Num_Data of {
    action_num : 'an,
    more : 'm
  }

fun action_num_data (action_num, more) =
  Action_Num_Data {action_num = action_num, more = more}

fun get_action_num (Action_Num_Data {action_num,...}) = action_num
fun map_action_num (f, (Action_Num_Data {action_num, more})) =
  Action_Num_Data {action_num = f action_num, more = more}
fun action_num _ = L.lens get_action_num map_action_num

fun get_more (Action_Num_Data {more,...}) = more
fun map_more (f, (Action_Num_Data {action_num,more})) =
  Action_Num_Data {action_num = action_num, more = f more}
fun more _ = L.lens get_more map_more

end

signature LIFT_ZIPPY_ACTION_NUM_DATA =
sig
  structure AND : ZIPPY_ACTION_NUM_DATA
  include ZIPPY_ACTION_NUM_DATA
  where type ('an, 'm) action_num_data = ('an, 'm) AND.action_num_data
end

functor Lift_Zippy_Action_Num_Data(
    structure AF : ARROW
    structure AND : ZIPPY_ACTION_NUM_DATA
    sharing type AND.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AT.cat
    val lift : ('p1, 'a, 'b) AF.cat -> ('p1, 'a, 'b) AT.cat
  ) : LIFT_ZIPPY_ACTION_NUM_DATA =
struct

structure AND = AND
structure L = L

type ('an, 'm) action_num_data = ('an, 'm) AND.action_num_data

fun action_num_data x = x |> lift AND.action_num_data
fun action_num_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (AND.get_action_num, AND.get_more)))
    action_num_data
fun action_num _ = L.lens_fst (action_num_data_lens ())
fun get_action_num x = x |> L.get (action_num ())
fun map_action_num x = x |> L.modify (action_num ())
fun more _ = L.lens_snd (action_num_data_lens ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end

