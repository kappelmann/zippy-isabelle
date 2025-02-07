(*  Title:      HOCLP/zippy_with_presults_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_WITH_PRESULTS_UTIL =
sig
  include ZIPPY_WITH_PRESULTS

  (* misc *)
  structure COU : COROUTINE_UTIL_APPLY
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) cat
  sharing type COU.acoroutine = CO.acoroutine

  val empty_ac : 'p1 COU.AE.exn -> ('p1, 'a, 'b) COU.coroutine

  (* copy *)
  (** run copies **)
  val get_run_copy : copy_update_data -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z3.zipper ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z1.zipper) hom_move

  val gen_copy_parent_actions :
    (*foldM*)
    (('pa -> ('p1, 'z, 'z) cat) -> 'pas -> ('p1, 'z, 'z) cat) ->
    (*copy parent action*)
    ('cud -> 'pa -> ('p1, 'z, 'z) cat) ->
    'cud -> 'pas -> ('p1, 'z, 'z) cat

  val copy_parent_actions :
    ((('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z3.zipper ->
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z1.zipper) hom_move) -> 'zs -> ('p1, 'z, 'z) cat) ->
    copy_update_data -> 'zs -> ('p1, 'z, 'z) cat

  (* actions *)
  val empty_paction : 'p1 COU.AE.exn -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction

  val gen_paction_from_presults :
    (*get presults*)
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults) cat ->
    (*action when results are empty*)
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action ->
    (*update zipper with pulled result and the remaining presults*)
    (result * ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action) ->
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction

  val paction_from_presults : ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action ->
    (result * ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action) ->
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction

  val update_result_tail_presults :
    (*update with pulled result*)
    (prio -> result -> ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, 'z) cat) ->
    (*update with remaining presults*)
    (prio -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults ->
      ('p1, 'z, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper) cat) ->
    result * ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action

  val gen_update_result :
    (*init child node*)
    (prio -> result -> ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, 'cud * 'ch) cat) ->
    (*get parent actions*)
    ('p1, 'ch, 'pas) cat ->
    (*copy parent actions*)
    ('cud -> 'pas -> ('p1, 'ch, 'z) cat) ->
    prio -> result -> ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, 'z) cat

  val presults_from_sq :
    (*coroutine in case of an empty sequence*)
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, result, prio) CO.acoroutine ->
    (*create next priority while optionally updating the sequence*)
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper * result Seq.seq,
      prio * result Seq.seq) CO.coroutine ->
    result Seq.seq -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults
end

functor Zippy_With_PResults_Util(
    structure Z : ZIPPY_WITH_PRESULTS
    structure AE : KLEISLI_ARROW_EXCEPTION
    sharing type AE.K.M.t = Z.K.M.t
  ) : ZIPPY_WITH_PRESULTS_UTIL =
struct

open Z

local
  structure SC = Semi_Category(Z); structure M = Monad(K.M);
  structure AAA = Kleisli_Arrow_Arrow_Apply(M); structure AC = Kleisli_Arrow_Choice(M)
  open SC M AAA AAA.A
in

(* misc *)
structure COU = Coroutine_Util_Apply(
  structure A = AAA
  structure CO = Coroutine_Util(structure AE = AE; structure CO = CO))

val empty_ac = COU.throw

(* copy *)
(** run copies **)
fun get_copy_data x = x |> (Z3.ZO.get_content >>> N3.get_content)

fun get_run_copy cud z3 z1 =
  get_copy_data z3 >>= CD.get_copy >>= arr (dest_copy #> (fn copy => (copy cud z3, z1))) >>= AA.app

fun gen_copy_parent_actions foldM copy_parent_action cud =
  foldM (fn ac => AE.try (copy_parent_action cud ac))

fun copy_parent_actions foldM = gen_copy_parent_actions foldM get_run_copy

(* actions *)
fun empty_paction e = AE.throw' e |> Z.mk_paction

fun gen_paction_from_presults get_aco empty_action update_result_tail_presults =
  let fun update_action rp_ac prio = AE.catch'
    (fn z => CO.resume rp_ac z
      >>= (apsnd mk_presults #> (fn r_ac => update_result_tail_presults r_ac prio z)))
    (empty_action prio)
  in
    (get_aco >>> arr (dest_presults #> CO.resume)) &&& id ()
    >>> AA.app
    >>> second (arr update_action)
    |> Z.mk_paction
  end

fun paction_from_presults empty_action = gen_paction_from_presults
  (Z4.ZO.get_content >>> N4.get_content >>> PAD.get_more >>> PRD.get_presults) empty_action

fun update_result_tail_presults update_result update_tail_aco (x, aco) prio =
  update_result prio x >>> update_tail_aco prio aco

fun gen_update_result init_child get_parent_actions copy_parent_actions prio x = init_child prio x
  >>> second (get_parent_actions &&& id ())
  >>> arr (fn (cud, (pas, d)) => (copy_parent_actions cud pas, d))
  >>> AA.app

(* structure AU = Alternating_Zippers5_Util(structure A = Z; structure CO = COU)

fun list_container_zippers3 x = x |>
  (AU.list_container_zippers Z3.ZM.Unzip.move Z3.ZM.Zip.move Z3.ZM.Down.move)

val test = Up1.move >>> Up5.move >>> Up4.move >>> list_container_zippers3

fun update_result init_child copy_parent_actions prio =
  gen_update_result init_child test copy_parent_actions prio *)

fun presults_from_sq aco_empty_sq mk_prio_sq_c sq =
  let
    fun update mk_prio_sq_c sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (CO.resume aco_empty_sq)
        (second (arr (presults_from_sq aco_empty_sq mk_prio_sq_c #> dest_presults)))
      |> CO.acoroutine
  in
    arr (rpair sq)
    >>> CO.resume mk_prio_sq_c
    >>> arr (fn ((prio, sq), mk_prio_sq_c) => (prio, update mk_prio_sq_c sq))
    |> CO.acoroutine |> mk_presults
  end

end

end
