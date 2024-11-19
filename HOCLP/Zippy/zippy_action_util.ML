(*  Title:      HOCLP/zippy_action_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_UTIL =
sig
  structure CO : COROUTINE

  val action_from_aco :
           (*update given data with pulled result and the tailing coroutine*)
    ('p -> ('p1, ('r * ('p1, 'd1, 'p, 'r) CO.acoroutine) * 'd1, 'd2) CO.C.cat) ->
    ('p1, 'd1, 'p, 'r) CO.acoroutine -> ('p1, 'd1, 'p * ('p1, 'd1, 'd2) CO.C.cat) CO.C.cat

  val update_data :
    (*update with pulled result*)
    ('p1, 'r * 'd1, 'd2) CO.C.cat ->
    (*update with tailing coroutine*)
    ('p1, 'aco * 'd2, 'd3) CO.C.cat ->
    ('p1, ('r * 'aco) * 'd1, 'd3) CO.C.cat

  val update_result :
    (*init child nod*)
    ('p1, 'd1, 'ui * 'ch) CO.C.cat ->
    (*get parent actions*)
    ('p1, 'ch, 'pas) CO.C.cat ->
    (*copy parent actions*)
    ('p1, 'pas * ('ui * 'ch), 'd2) CO.C.cat ->
    ('p1, 'd1, 'd2) CO.C.cat

  val copy_parent_actions :
    (*next parent action*)
    ('p1, 'pas, 'pa * 'pas) CO.C.cat ->
    (*copy parent action*)
    ('p1, 'pa * 'd, 'd) CO.C.cat ->
    (*add and init parent action*)
    ('p1, 'pas * 'd, 'd) CO.C.cat

  val update_aco :
    (*make new node*)
    ('p1, 'aco * 'd1, 'n) CO.C.cat ->
    (*add new node*)
    ('p1, 'n * 'd1, 'd2) CO.C.cat ->
    (*update data with tailing coroutine*)
    ('p1, 'aco * 'd2, 'd3) CO.C.cat ->
    ('p1, 'aco * 'd1, 'd3) CO.C.cat

  val aco_from_sq :
    (*empty coroutine*)
    ('p1, 'd, 'r, 'p) CO.acoroutine ->
    (*create next priority while optionally updating the sequence*)
    ('p1, 'd * 'r Seq.seq, 'p * 'r Seq.seq) CO.coroutine ->
    'r Seq.seq -> ('p1, 'd, 'p, 'r) CO.acoroutine
end

functor Zippy_Action_Util(
    structure A : ARROW
    structure AC : ARROW_CHOICE
    sharing type AC.cat = A.cat
    structure AE : ARROW_EXCEPTION_REC
    sharing type AE.cat = A.cat
    structure CO : COROUTINE
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
  ) : ZIPPY_ACTION_UTIL =
struct

structure CO = CO

local structure SC = Semi_Category(A) open SC A
in
fun action_from_aco update_data aco =
  let fun update_action prio rp_ac = (CO.resume rp_ac &&& id ()) >>> update_data prio
  in CO.resume aco >>> A.arr (fn (prio, rp_ac) => (prio, update_action prio rp_ac)) end

fun update_data update_result update_aco =
  arr (fn ((x, mk_action), data) => (mk_action, (x, data)))
  >>> second update_result
  >>> update_aco

fun update_result init_child get_parent_actions copy_parent_actions = init_child
  >>> second (get_parent_actions &&& id ())
  >>> arr (fn (ui, (pas, d)) => (pas, (ui, d)))
  >>> copy_parent_actions

fun copy_parent_actions next_action copy_parent_action =
  AE.repeat (
    first next_action
    >>> arr (fn ((ac, acs), uid) => (acs, (ac, uid)))
    >>> second copy_parent_action)
  >>> arr snd

fun update_aco mk_node add_node update_aco =
  arr (fn (ac, data) => (ac, (ac, data)))
  >>> second (mk_node &&& arr snd >>> add_node)
  >>> update_aco

fun aco_from_sq aco_empty_sq mk_prio_sq_c sq =
  let
    fun update mk_prio_sq_c sq =
      arr (fn data => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K data))
      >>> AC.merge (CO.resume aco_empty_sq) (second (arr (aco_from_sq aco_empty_sq mk_prio_sq_c)))
      |> CO.acoroutine
  in
    arr (rpair sq)
    >>> CO.resume mk_prio_sq_c
    >>> arr (fn ((prio, sq), mk_prio_sq_c) => (prio, update mk_prio_sq_c sq))
    |> CO.acoroutine
  end

end

end
