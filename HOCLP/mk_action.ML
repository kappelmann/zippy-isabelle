(*  Title:      HOCLP/mk_action.ML
    Author:     Kevin Kappelmann
*)
signature CONTENT_MK_ACTION =
sig
  type ('c, 'ma) cma
  val mk_content_mk_action: 'c -> 'ma -> ('c, 'ma) cma

  val get_content : ('c, 'ma) cma -> 'c
  val get_mk_action : ('c, 'ma) cma -> 'ma

  val map_content : ('c1 -> 'c2) -> ('c1, 'ma) cma -> ('c2, 'ma) cma
  val map_mk_action : ('ma1 -> 'ma2) -> ('c, 'ma1) cma -> ('c, 'ma2) cma

  val content : unit -> (('c2, 'ma) cma, 'c2, ('c1, 'ma) cma, 'c1) SLens.lens
  val mk_action : unit -> (('c, 'ma2) cma, 'ma2, ('c, 'ma1) cma, 'ma1) SLens.lens
end

structure Content_Mk_Action : CONTENT_MK_ACTION =
struct
  datatype ('c, 'ma) cma = CMA of {
    content : 'c,
    mk_action : 'ma
  }
  fun mk_content_mk_action content mk_action = CMA {content = content, mk_action = mk_action}

  fun get_content (CMA {content,...}) = content
  fun get_mk_action (CMA {mk_action,...}) = mk_action
  fun map_content f (CMA {content, mk_action}) =
    CMA {content = f content, mk_action = mk_action}
  fun map_mk_action f (CMA {content, mk_action}) =
    CMA {content = content, mk_action = f mk_action}

  fun content _ = SLens.lens get_content (uncurry map_content)
  fun mk_action _ = SLens.lens get_mk_action (uncurry map_mk_action)
end

signature MK_ACTION =
sig
  include MOVE_BASE

  type ('p, 'i, 'a, 'b, 'c, 'd) data
  type ('p, 'i, 'a, 'b, 'c, 'd) to = 'p * ('i, ('p, 'i, 'a, 'b, 'c, 'd) data) hom_move

  type ('p, 'i, 'a, 'b, 'c, 'd) mk_action
  val mk_action : ('i, ('p, 'i, 'a, 'b, 'c, 'd) data, ('p, 'i, 'a, 'b, 'c, 'd) to) move ->
    ('p, 'i, 'a, 'b, 'c, 'd) mk_action
  val dest_mk_action : ('p, 'i, 'a, 'b, 'c, 'd) mk_action ->
    ('i, ('p, 'i, 'a, 'b, 'c, 'd) data, ('p, 'i, 'a, 'b, 'c, 'd) to) move
end

functor Mk_Action(
    structure M : MOVE_BASE
    type ('i, 'a, 'b, 'c, 'd, 'ma) data
  ) : MK_ACTION =
struct

open M

datatype ('p, 'i, 'a, 'b, 'c, 'd) mk_action = Mk_Action of ('i,
  ('i, 'a, 'b, 'c, 'd, ('p, 'i, 'a, 'b, 'c, 'd) mk_action) data,
  'p * ('i, ('i, 'a, 'b, 'c, 'd, ('p, 'i, 'a, 'b, 'c, 'd) mk_action) data) hom_move)
  move
type ('p, 'i, 'a, 'b, 'c, 'd) data = ('i, 'a, 'b, 'c, 'd, ('p, 'i, 'a, 'b, 'c, 'd) mk_action) data
type ('p, 'i, 'a, 'b, 'c, 'd) to = 'p * ('i, ('p, 'i, 'a, 'b, 'c, 'd) data) hom_move

fun mk_action mka = Mk_Action mka
fun dest_mk_action (Mk_Action mka) = mka

end

signature MK_ACTION_UTIL =
sig
  structure AE : IARROW_EXCEPTION_BASE
  structure MA : MK_ACTION
  sharing type MA.cat = AE.cat
  structure CO : ICOROUTINE
  sharing type CO.C.cat = AE.cat

  type ('p, 'x, 'i, 'a, 'b, 'c, 'd) pd_ac =
    ('i, 'i, ('p, 'i, 'a, 'b, 'c, 'd) MA.data, 'p, 'x) CO.acoroutine

  val mk_action_from_ac : ('p ->
    (*update given data with pulled 'x and the tailing coroutine*)
    ('i, ('x * ('p, 'x, 'i, 'a, 'b, 'c, 'd) pd_ac) * ('p, 'i, 'a, 'b, 'c, 'd) MA.data,
      ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move) ->
    (*get coroutine*)
    ('i, ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'x, 'i, 'a, 'b, 'c, 'd) pd_ac) MA.move ->
    ('p, 'i, 'a, 'b, 'c, 'd) MA.mk_action

  val update_data :
    (*update with pulled data*)
    ('i, 'x * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move ->
    (*update with tailing coroutine*)
    ('i, 'ac * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move ->
    ('i, ('x * 'ac) * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move

  val update_ac :
    (*make new child node*)
    ('i, 'ac * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, 'ch) MA.move ->
    (*add child node to data*)
    ('i, 'ch * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move ->
    (*update data with tailing coroutine*)
    ('i, 'ac * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move ->
    ('i, 'ac * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.move

  val throw_mk_action : AE.exn -> ('p, 'i, 'a, 'b, 'c, 'd) MA.mk_action
  val set_throw_mk_action : AE.exn -> (('p, 'i, 'a, 'b, 'c, 'd) MA.mk_action -> 'r) -> 'r
  val disable_mk_aktion_update_ac : AE.exn ->
    (*set disabled action*)
    (('p, 'i, 'a, 'b, 'c, 'd) MA.mk_action -> ('i, ('p, 'i, 'a, 'b, 'c, 'd) MA.data) MA.hom_move) ->
    (*update with tailing coroutine*)
    ('i, 'ac * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, 'r) MA.move ->
    ('i, 'ac * ('p, 'i, 'a, 'b, 'c, 'd) MA.data, 'r) MA.move

  val ac_from_sq : ('i, 'i, 'd, 'x, 'p) CO.acoroutine ->
    ('i, 'i, 'd * 'x Seq.seq, 'p * 'x Seq.seq) CO.coroutine -> ('i, 'd, 'x Seq.seq) MA.move ->
    ('i, 'i, 'd, 'p, 'x) CO.acoroutine

end

functor Mk_Action_Util(
    structure A : IARROW
    structure AA : IARROW_APPLY_BASE
    sharing type AA.cat = A.cat
    structure AC : IARROW_CHOICE
    sharing type AC.cat = A.cat
    structure AE : IARROW_EXCEPTION
    sharing type AE.cat = A.cat
    structure MA : MK_ACTION
    sharing type MA.cat = A.cat
    structure CO : ICOROUTINE
    sharing type CO.C.cat = A.cat
  ) : MK_ACTION_UTIL =
struct

structure AE = AE
structure MA = MA
structure CO = CO

type ('p, 'x, 'i, 'a, 'b, 'c, 'd) pd_ac =
  ('i, 'i, ('p, 'i, 'a, 'b, 'c, 'd) MA.data, 'p, 'x) CO.acoroutine

local structure SC = ISemi_Category(A) open SC A
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

fun disable_mk_aktion_update_ac e set_mk_action update_ac =
  second (set_throw_mk_action e set_mk_action)
  >>> update_ac

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

end


(* fun with_parent_content mk_action zipper = Up2.K.M.bind (Up2.move zipper)
  (fn parent => let val content = L.get (L.content1 ()) parent in mk_action content zipper end) *)

(*structure L =
struct
  open SLens
  fun content1 _ = Z1.content () |> comp (N1.content ())
  fun next1 _ = Z1.content () |> comp (N1.next ())
  fun content2 _ = Z2.content () |> comp (N2.content ()) |> comp (ncontent2 ())
  fun next2 _ = Z2.content () |> comp (N2.next ())
  fun mk_action _ = content2 () |> comp (CMA.mk_action ())
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
