(*  Title:      HOCLP/zippy.ML
    Author:     Kevin Kappelmann
*)
(* functor Zippy(
    structure CO : COROUTINE
    structure AZ : ALTERNATING_ZIPPERS4
    sharing type AZ.cat = CO.C.cat
  ) =
struct

structure CO = CO
structure AZ = AZ

structure A = Zippy_Action
structure AC = Zippy_Action_Cluster

datatype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) action = Action of ('p1,
  ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4,
  'p * ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4) AZ.hom_move) AZ.cat
withtype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) action, 'a4) A.action) AZ.Z4.zipper
type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) action, 'a4) A.action) AZ.Z1.zipper
type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper2 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) action, 'a4) A.action) AZ.Z2.zipper
type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) action, 'a4) A.action) AZ.Z3.zipper

fun mk_action action = Action action
fun run_action (Action action) = action

datatype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) copy = Copy of
  ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper1) AZ.hom_move
withtype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'a1, 'a2, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) AC.acluster, 'a4) zipper1

local type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4, 'r) aco_functor =
  ('p1, ('p1, 'a1, 'a2, ('r, 'r) AC.acluster, 'a4) AZ.Z4.zipper, 'p, 'x) CO.acoroutine
in
datatype ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac = Ac of ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac
withtype ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac =
  ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac) aco_functor
end

fun ac x = Ac x
fun dest_ac (Ac ac) = ac

signature MK_ACTION =
sig
  structure C : SEMI_CATEGORY_BASE
  type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data
  type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) to = 'p *
    ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data) C.cat

  type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) mk_action
  val mk_action : ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data,
    ('p1, 'p, 'a1, 'a2, 'a3, 'a4) to) C.cat -> ('p1, 'p, 'a1, 'a2, 'a3, 'a4) mk_action
  val run : ('p1, 'p, 'a1, 'a2, 'a3, 'a4) mk_action ->
    ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) to) C.cat
end

signature MK_ACTION_UTIL =
sig
  structure AE : ARROW_EXCEPTION_BASE
  structure MA : MK_ACTION
  sharing type MA.C.cat = AE.cat
  structure CO : COROUTINE
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AE.cat

  type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pd_ac =
    ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, 'p, 'x) CO.acoroutine

  val mk_action_from_ac : ('p ->
    (*update given data with pulled 'x and the tailing coroutine*)
    ('p1, ('x * ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pd_ac) * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data,
      ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat) ->
    (*get coroutine*)
    ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pd_ac) MA.C.cat ->
    ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.mk_action

  val update_data :
    (*update with pulled data*)
    ('p1, 'x * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat ->
    (*update with tailing coroutine*)
    ('p1, 'ac * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat ->
    ('p1, ('x * 'ac) * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat

  val update_ac :
    (*make new child node*)
    ('p1, 'ac * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, 'ch) MA.C.cat ->
    (*add child node to data*)
    ('p1, 'ch * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat ->
    (*update data with tailing coroutine*)
    ('p1, 'ac * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat ->
    ('p1, 'ac * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat

  val throw_mk_action : AE.exn -> ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.mk_action
  val set_throw_mk_action : AE.exn -> (('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.mk_action -> 'r) -> 'r
  val update_ac_disable_mk_action : AE.exn ->
    (*set disabled action*)
    (('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.mk_action ->
      ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat) ->
    (*update with tailing coroutine*)
    ('p1, 'ac * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat ->
    ('p1, 'ac * ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data) MA.C.cat

  val ac_from_sq : ('p1, 'd, 'x, 'p) CO.acoroutine ->
    ('p1, 'd * 'x Seq.seq, 'p * 'x Seq.seq) CO.coroutine -> ('p1, 'd, 'x Seq.seq) MA.C.cat ->
    ('p1, 'd, 'p, 'x) CO.acoroutine

end

functor Mk_Action_Util(
    structure A : ARROW
    structure AA : ARROW_APPLY_BASE
    sharing type AA.cat = A.cat
    structure AC : ARROW_CHOICE
    sharing type AC.cat = A.cat
    structure AE : ARROW_EXCEPTION
    sharing type AE.cat = A.cat
    structure MA : MK_ACTION
    sharing type MA.C.cat = A.cat
    structure CO : COROUTINE
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
  ) : MK_ACTION_UTIL =
struct

structure AE = AE
structure MA = MA
structure CO = CO

type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pd_ac =
  ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) MA.data, 'p, 'x) CO.acoroutine

local structure SC = Semi_Category(A) open SC A
in
fun mk_action_from_ac update_data get_ac =
  let fun update_action prio dp_ac = CO.resume dp_ac &&& id ()
    >>> update_data prio
  in
    (get_ac >>> arr CO.resume) &&& id ()
    >>> AA.app
    >>> A.arr (fn (prio, dp_ac) => (prio, update_action prio dp_ac))
    |> MA.mk_action
  end

fun update_data update_pulled update_ac =
  arr (fn ((x, mk_action), data) => (mk_action, (x, data)))
  >>> second update_pulled
  >>> update_ac

fun update_ac mk_child add_child update_ac =
  arr (fn (ac, data) => (ac, (ac, data)))
  >>> second (mk_child &&& arr snd >>> add_child)
  >>> update_ac

fun throw_mk_action e = AE.throw' e |> MA.mk_action
fun set_throw_mk_action e set_mk_action = throw_mk_action e |> set_mk_action

fun update_ac_disable_mk_action e set_mk_action update_ac = update_ac
  >>> set_throw_mk_action e set_mk_action

fun ac_from_sq ac_empty_sq mk_prio_sq_c get_sq =
  let
    fun update mk_prio_sq_c sq =
      arr (fn data => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K data))
      >>> AC.merge (CO.resume ac_empty_sq) (second (arr (K #> ac_from_sq ac_empty_sq mk_prio_sq_c)))
      |> CO.acoroutine
  in
    id () &&& get_sq
    >>> CO.resume mk_prio_sq_c
    >>> arr (fn ((prio, sq), mk_prio_sq_c) => (prio, update mk_prio_sq_c sq))
    |> CO.acoroutine
  end

end

end *)

(* fun bfs_base finish_node bfs_children move_down move_right node contsq childrensq =
  let
    val childrensq =
      Seq.make (fn () => move_down node |> seq_of_opt |> Seq.append childrensq |> Seq.pull)
    val bfs = bfs_base finish_node bfs_children move_down move_right
    val nextsq = Seq.make (fn () => (case move_right node of
        SOME node => bfs node contsq childrensq
      | NONE => case Seq.pull contsq of
          SOME (node, contsq) => bfs node contsq childrensq
        | NONE => case Seq.pull childrensq of
            SOME (child, childrensq) => bfs_children child childrensq Seq.empty
          | NONE => Seq.empty)
      |> Seq.pull)
  in finish_node node nextsq end

fun bfs_tac_tree path_tac_tree_zipper = bfs_base (K I) bfs_tree
  move_down_path_tac_tree_zipper move_right_path_tac_tree_zipper path_tac_tree_zipper
and bfs_tree path_tree_zipper = bfs_base Seq.cons bfs_tac_tree
  move_down_path_tree_zipper move_right_path_tree_zipper path_tree_zipper *)

