(*  Title:      HOCLP/mk_action.ML
    Author:     Kevin Kappelmann
*)
structure Content_Mk_Action =
struct
  datatype ('c, 'ma) cma = CMA of {
    content : 'c,
    mk_action : 'ma
  }
  fun mk_content content mk_action = CMA {content = content, mk_action = mk_action}

  fun get_content (CMA {content,...}) = content
  fun get_mk_action (CMA {mk_action,...}) = mk_action
  fun map_content f (CMA {content, mk_action}) =
    CMA {content = f content, mk_action = mk_action}
  fun map_mk_action f (CMA {content, mk_action}) =
    CMA {content = content, mk_action = f mk_action}

  fun content _ = SLens.lens get_content (uncurry map_content)
  fun mk_action _ = SLens.lens get_mk_action (uncurry map_mk_action)
end

functor Mk_Action(
  structure M : IMONAD_BASE
  type ('i, 'a, 'b, 'ma) zipperma
  (* structure AZ : ALTERNATING_BI_ZIPPERS_BI_NODES *)
  (* sharing type AZ.Z2.K.M.t = ME.t *)
  (* val ncontent2 : unit -> (('a, 'b, 'c) AZ.N2.content, 'b, ('a, 'b, 'c) AZ.N2.content, 'b) SLens.lens *)
) =
struct

structure MB = Move_Base(IKleisli(M))

local type ('p, 'i, 'a, 'b, 'ma) to = 'p * ('i, ('i, 'a, 'b, 'ma) zipperma) MB.hom_move
in
datatype ('p, 'i, 'a, 'b) mk_action = Mk_Action of ('i,
  ('i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) zipperma,
  ('p, 'i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) to)
  MB.move

val mk_action = Mk_Action
fun dest_mk_action (Mk_Action ma) = ma

local type ('p, 'i, 'a, 'b) zipper = ('i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) zipperma
in
structure Coroutine = ICoroutine(IKleisli_IArrow_Apply(M))
type ('p, 'i, 'a, 'b) mk_actionc = ('i,
  ('p, 'i, 'a, 'b) zipper,
  ('p, 'i, 'a, 'b, ('p, 'i, 'a, 'b) mk_action) to)
  Coroutine.coroutine
end
end

(* fun action_ord x = x |> HOCLP_Util.fst_ord Prio.ord *)

local structure M = IMonad(M) open M
in

(*invariant: append returns the zipper at the same position*)
fun mk_action_mk_actionc zappend mk_new_content (mk_actionc  : ('p, 'i, 'a, 'b) mk_actionc) =
  let
    fun update_action prio action mk_actionc =
      let fun append_child zipper =
        let val content =
          mk_new_content zipper prio (mk_action_mk_actionc zappend mk_new_content mk_actionc)
        in zappend content zipper end
      in append_child >=> action end
  in
    Coroutine.resume mk_actionc
    >=> (fn ((prio, action), mk_actionc) => pure (prio, update_action prio action mk_actionc))
    |> mk_action
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
