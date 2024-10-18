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

  type ('p, 'i, 'a, 'b) data
  type ('p, 'i, 'a, 'b) to = 'p * ('i, ('p, 'i, 'a, 'b) data) hom_move

  type ('p, 'i, 'a, 'b) mk_action
  val mk_action : ('i, ('p, 'i, 'a, 'b) data, ('p, 'i, 'a, 'b) to) move ->
    ('p, 'i, 'a, 'b) mk_action
  val dest_mk_action : ('p, 'i, 'a, 'b) mk_action ->
    ('i, ('p, 'i, 'a, 'b) data, ('p, 'i, 'a, 'b) to) move
end

functor Mk_Action(
    structure M : MOVE_BASE
    type ('i, 'a, 'b, 'ma) data
  ) : MK_ACTION =
struct

open M

datatype ('p, 'i, 'a, 'b) mk_action = Mk_Action of ('i,
  ('i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) data,
  'p * ('i, ('i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) data) hom_move)
  move
type ('p, 'i, 'a, 'b) data = ('i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) data
type ('p, 'i, 'a, 'b) to = 'p * ('i, ('p, 'i, 'a, 'b) data) hom_move

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

  val mk_action_from_ac : ('p ->
    (*updates given data with pulled 'c and the mk_action created from the tailing coroutine*)
    ('i, ('p, 'i, 'a, 'b) MA.data * ('c * ('p, 'i, 'a, 'b) MA.mk_action),
      ('p, 'i, 'a, 'b) MA.data) MA.move) ->
    ('i, 'i, ('p, 'i, 'a, 'b) MA.data, 'p, 'c) CO.acoroutine -> ('p, 'i, 'a, 'b) MA.mk_action

  val update_data :
    (*update with pulled data*)
    ('i, 'c * ('p, 'i, 'a, 'b) MA.data, ('p, 'i, 'a, 'b) MA.data) MA.move ->
    (*update with new mk_action data*)
    ('i, ('p, 'i, 'a, 'b) MA.mk_action * ('p, 'i, 'a, 'b) MA.data,
      ('p, 'i, 'a, 'b) MA.data) MA.move ->
    ('i, ('p, 'i, 'a, 'b) MA.data * ('c * ('p, 'i, 'a, 'b) MA.mk_action),
      ('p, 'i, 'a, 'b) MA.data) MA.move

  val throw_mk_action : AE.exn -> ('p, 'i, 'a, 'b) MA.mk_action
  val set_throw_mk_action : AE.exn -> (('a, 'b, 'c, 'd) MA.mk_action -> 'r) -> 'r
  val update_mk_action : AE.exn ->
    (('p, 'i, 'a, 'b) MA.mk_action -> ('i, ('p, 'i, 'a, 'b) MA.data) MA.hom_move) ->
    ('i, 'c * ('p, 'i, 'a, 'b) MA.data, 'r) MA.move ->
    ('i, 'c * ('p, 'i, 'a, 'b) MA.data, 'r) MA.move

  val update_new_mk_action :
    ('i, ('p, 'i, 'a, 'b) MA.mk_action * ('p, 'i, 'a, 'b) MA.data, 'ch) MA.move ->
    ('i, 'ch * ('p, 'i, 'a, 'b) MA.data, ('p, 'i, 'a, 'b) MA.data) MA.move ->
    ('i, ('p, 'i, 'a, 'b) MA.mk_action * ('p, 'i, 'a, 'b) MA.data, ('p, 'i, 'a, 'b) MA.data) MA.move

  val ac_from_sq : ('d -> 'c Seq.seq -> 'p * 'c Seq.seq) -> ('i, 'i, 'd, 'c, 'p) CO.acoroutine ->
    'c Seq.seq -> ('i, 'i, 'd, 'p, 'c) CO.acoroutine
end

functor Mk_Action_Util(
    structure A : IARROW
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

local structure SC = ISemi_Category(A) open SC A
in
fun mk_action_from_ac update_data pd_ac =
  let fun update_action prio dp_ac = id () &&& CO.resume dp_ac
    >>> A.second (A.second (A.arr (mk_action_from_ac update_data)))
    >>> update_data prio
  in
    CO.resume pd_ac
    >>> A.arr (fn (prio, dp_ac) => (prio, update_action prio dp_ac))
    |> MA.mk_action
  end

fun update_data update_pulled update_mk_action =
  arr (fn (data, (x, mk_action)) => (mk_action, (x, data)))
  >>> second update_pulled
  >>> update_mk_action

fun throw_mk_action e = AE.throw' e |> MA.mk_action
fun set_throw_mk_action e set_mk_action = throw_mk_action e |> set_mk_action

fun update_mk_action e set_mk_action update_new_mk_action =
  second (set_throw_mk_action e set_mk_action)
  >>> update_new_mk_action

fun update_new_mk_action mk_child append = (mk_child &&& arr snd) >>> append

fun ac_from_sq mk_prio_sq ac_empty_sq sq =
  let
    fun update sq = arr (fn zipper => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K zipper))
      >>> AC.merge (CO.resume ac_empty_sq) (second (arr (ac_from_sq mk_prio_sq ac_empty_sq)))
      |> CO.acoroutine
  in
    arr (fn data => mk_prio_sq data sq ||> update)
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
