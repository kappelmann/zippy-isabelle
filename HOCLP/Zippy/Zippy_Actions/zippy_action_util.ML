(*  Title:      HOCLP/zippy_action_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_UTIL =
sig
  structure AE : KLEISLI_ARROW_EXCEPTION
  structure CO : COROUTINE
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AE.cat

  val paction_from_aco :
    (*action when results are empty*)
    ('p1, 'd1, 'd2) AE.cat ->
    (*update given data with pulled result and the tailing coroutine*)
    ('p -> 'r * ('p1, 'd1, 'p, 'r) CO.acoroutine -> ('p1, 'd1, 'd2) AE.cat) ->
    ('p1, 'd1, ('p1, 'd1, 'p, 'r) CO.acoroutine) AE.cat ->
    ('p1, 'd1, 'p * ('p -> ('p1, 'd1, 'd2) AE.cat)) AE.cat

  val update_result_tail_aco :
    (*update with pulled result*)
    ('r -> ('p1, 'd1, 'd2) AE.cat) ->
    (*update with tailing coroutine*)
    ('aco -> ('p1, 'd2, 'd3) AE.cat) ->
    'r * 'aco -> ('p1, 'd1, 'd3) AE.cat

  val update_result :
    (*init child node*)
    ('r -> ('p1, 'd1, 'cud * 'ch) AE.cat) ->
    (*get parent actions*)
    ('p1, 'ch, 'pas) AE.cat ->
    (*copy parent actions*)
    ('cud -> 'pas -> ('p1, 'ch, 'd2) AE.cat) ->
    'r -> ('p1, 'd1, 'd2) AE.cat

  val copy_parent_actions :
    (*foldM*)
    (('pa -> ('p1, 'd, 'd) AE.cat) -> 'pas -> ('p1, 'd, 'd) AE.cat) ->
    (*copy parent action*)
    ('cud -> 'pa -> ('p1, 'd, 'd) AE.cat) ->
    'cud -> 'pas -> ('p1, 'd, 'd) AE.cat

  val aco_from_sq :
    (*coroutine in case of an empty sequence*)
    ('p1, 'd, 'r, 'p) CO.acoroutine ->
    (*create next priority while optionally updating the sequence*)
    ('p1, 'd * 'r Seq.seq, 'p * 'r Seq.seq) CO.coroutine ->
    'r Seq.seq -> ('p1, 'd, 'p, 'r) CO.acoroutine
end

functor Zippy_Action_Util(
    structure AE : KLEISLI_ARROW_EXCEPTION
    structure CO : COROUTINE
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AE.cat
  ) : ZIPPY_ACTION_UTIL =
struct

structure CO = CO
structure AE = AE

local
  structure SC = Semi_Category(AE); structure M = AE.K.M; structure A = Kleisli_Arrow(M)
  structure AA = Kleisli_Arrow_Apply(M); structure AC = Kleisli_Arrow_Choice(M)
  open SC A
in
fun paction_from_aco empty_action update_result_tail_aco get_aco =
  let fun update_action rp_ac prio = AE.catch'
    ((CO.resume rp_ac &&& id ()) >>> AA.uncurry (update_result_tail_aco prio))
    empty_action
  in
    (get_aco >>> arr CO.resume) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
  end

fun update_result_tail_aco update_result update_tail_aco (x, aco) =
  update_result x >>> update_tail_aco aco

fun update_result init_child get_parent_actions copy_parent_actions x = init_child x
  >>> second (get_parent_actions &&& id ())
  >>> arr (fn (cud, (pas, d)) => (copy_parent_actions cud pas, d))
  >>> AA.app

fun copy_parent_actions foldM copy_parent_action cud =
  foldM (fn ac => AE.try (copy_parent_action cud ac))

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
