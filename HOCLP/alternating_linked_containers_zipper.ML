(*  Title:      HOCLP/alternating_linked_containers_zipper.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_LINKED_CONTAINERS_ZIPPER =
sig
  structure ALC : ALTERNATING_LINKED_CONTAINERS

  type ('c1, 'c2) lzcontext1
  type ('c1, 'c2) lzcontext2
  type ('c1, 'c2) zcontext1
  type ('c1, 'c2) zcontext2

  structure ZD : ZIPPER_DATA
  (*parent monads*)
  structure PM1 : MONAD_BASE
  structure PM2 : MONAD_BASE

  type ('c1, 'c2) parent1 = (('c2, ('c1, 'c2) zcontext2) ZD.zipper) PM1.t
  type ('c1, 'c2) parent2 = (('c1, ('c1, 'c2) zcontext1) ZD.zipper) PM2.t

  val zcontext1 : ('c1, 'c2) lzcontext1 -> ('c1, 'c2) parent1 -> ('c1, 'c2) zcontext1
  val zcontext2 : ('c1, 'c2) lzcontext2 -> ('c1, 'c2) parent2 -> ('c1, 'c2) zcontext2

  structure Z1 : BI_ZIPPER
  where type ('c1, 'c2) content = ('c1, 'c2) ALC.node1
  where type ('c1, 'c2) zcontext = ('c1, 'c2) zcontext1
  where type ('c1, 'c2) container = ('c1, 'c2) ALC.anodes1 * ('c1, 'c2) parent1

  structure Z2 : BI_ZIPPER
  where type ('c1, 'c2) content = ('c1, 'c2) ALC.node2
  where type ('c1, 'c2) zcontext = ('c1, 'c2) zcontext2
  where type ('c1, 'c2) container = ('c1, 'c2) ALC.anodes2 * ('c1, 'c2) parent2

  structure Down1 : BI_ZIPPER_MOVE
  where type ('c1, 'c2) from = ('c1, 'c2) Z1.zipper
  where type ('c1, 'c2) to = ('c1, 'c2) Z2.zipper
  sharing type Down1.K.M.t = Z2.Init.K.M.t

  structure Down2 : BI_ZIPPER_MOVE
  where type ('c1, 'c2) from = ('c1, 'c2) Z2.zipper
  where type ('c1, 'c2) to = ('c1, 'c2) Z1.zipper
  sharing type Down2.K.M.t = Z1.Init.K.M.t

  structure Up1 : BI_ZIPPER_MOVE
  where type ('c1, 'c2) from = ('c1, 'c2) Z1.zipper
  where type ('c1, 'c2) to = ('c1, 'c2) Z2.zipper
  sharing type Up1.K.M.t = PM1.t

  structure Up2 : BI_ZIPPER_MOVE
  where type ('c1, 'c2) from = ('c1, 'c2) Z2.zipper
  where type ('c1, 'c2) to = ('c1, 'c2) Z1.zipper
  sharing type Up2.K.M.t = PM2.t

end

functor Alternating_Linked_Containers_Zipper(
    structure ALC : ALTERNATING_LINKED_CONTAINERS
    structure ZD : ZIPPER_DATA
    structure PM1 : MONAD_BASE
    structure PM2 : MONAD_BASE

    structure Z1 : ZIPPER
    where type 'a content = 'a
    sharing type ALC.N1.C.container = Z1.container

    structure Z2 : ZIPPER
    where type 'a content = 'a
    sharing type ALC.N2.C.container = Z2.container)
  :
  sig
    include ALTERNATING_LINKED_CONTAINERS_ZIPPER
    sharing type Z1.K.M.t = Z1.K.M.t
    sharing type Z2.K.M.t = Z2.K.M.t
  end =
struct

structure ALC = ALC

structure ZD = ZD
structure PM1 = PM1
structure PM2 = PM2

type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

structure BZ1 = Bi_Zipper_Zipper(type ('c1, 'c2) content = ('c1, 'c2) ALC.node1; structure Z = Z1)
structure BZ2 = Bi_Zipper_Zipper(type ('c1, 'c2) content = ('c1, 'c2) ALC.node2; structure Z = Z2)

type ('c1, 'c2) lzcontext1 = ('c1, 'c2) BZ1.zcontext
type ('c1, 'c2) lzcontext2 = ('c1, 'c2) BZ2.zcontext

datatype ('c1, 'c2) zcontext1 = ZContext1 of (
    ('c1, 'c2) lzcontext1,
    (('c2, ('c1, 'c2) zcontext2) ZD.zipper) PM1.t
  ) lzcontext_parent
and ('c1, 'c2) zcontext2 = ZContext2 of (
    ('c1, 'c2) lzcontext2,
    (('c1, ('c1, 'c2) zcontext1) ZD.zipper) PM2.t
  ) lzcontext_parent

type ('c1, 'c2) parent1 = (('c2, ('c1, 'c2) zcontext2) ZD.zipper) PM1.t
type ('c1, 'c2) parent2 = (('c1, ('c1, 'c2) zcontext1) ZD.zipper) PM2.t

fun zcontext1 lzcontext parent = ZContext1 (lzcontext_parent lzcontext parent)
fun zcontext2 lzcontext parent = ZContext2 (lzcontext_parent lzcontext parent)

fun get_zcontext1_lzcontext (ZContext1 {lzcontext, ...}) = lzcontext
fun get_zcontext1_parent (ZContext1 {parent, ...}) = parent

fun get_zcontext2_lzcontext (ZContext2 {lzcontext, ...}) = lzcontext
fun get_zcontext2_parent (ZContext2 {parent, ...}) = parent

structure RBZ1 = Replace_Bi_Zipper_Container(
  structure Z = BZ1
  type ('c1, 'c2) ncontainer = ('c1, 'c2) ALC.anodes1
  val ncontainer = ALC.anodes1
  val dest_ncontainer = ALC.get_nodes1
)
structure Z1 = Extend_Bi_Zipper_Context(
  structure ZD = ZD
  structure Z = RBZ1
  type ('c1, 'c2) new_zcontext = ('c1, 'c2) parent1
  type ('c1, 'c2) zcontext = ('c1, 'c2) zcontext1
  val zcontext = zcontext1
  val get_old_zcontext = get_zcontext1_lzcontext
  val get_new_zcontext = get_zcontext1_parent
)

structure RBZ2 = Replace_Bi_Zipper_Container(
  structure Z = BZ2
  type ('c1, 'c2) ncontainer = ('c1, 'c2) ALC.anodes2
  val ncontainer = ALC.anodes2
  val dest_ncontainer = ALC.get_nodes2
)
structure Z2 = Extend_Bi_Zipper_Context(
  structure ZD = ZD
  structure Z = RBZ2
  type ('c1, 'c2) new_zcontext = ('c1, 'c2) parent2
  type ('c1, 'c2) zcontext = ('c1, 'c2) zcontext2
  val zcontext = zcontext2
  val get_old_zcontext = get_zcontext2_lzcontext
  val get_new_zcontext = get_zcontext2_parent
)

fun down pure get_content get_zcontext dest_node init zipper =
  let
    val {content, next} = get_content zipper |> dest_node
    val parent = ZD.zipper content (get_zcontext zipper) |> pure
  in init (next, parent) end

structure Down1 : BI_ZIPPER_MOVE =
struct
  structure ZMB = Zipper_Move_Base(Z2.Init.K)
  open ZMB
  type ('c1, 'c2) from = ('c1, 'c2) Z1.zipper
  type ('c1, 'c2) to = ('c1, 'c2) Z2.zipper
  fun move zipper =
    down PM2.pure Z1.get_content Z1.get_zcontext ALC.N1.N.dest_node Z2.Init.move zipper
end
structure Down2 : BI_ZIPPER_MOVE =
struct
  structure ZMB = Zipper_Move_Base(Z1.Init.K)
  open ZMB
  type ('c1, 'c2) from = ('c1, 'c2) Z2.zipper
  type ('c1, 'c2) to = ('c1, 'c2) Z1.zipper
  fun move zipper =
    down PM1.pure Z2.get_content Z2.get_zcontext ALC.N2.N.dest_node Z1.Init.move zipper
end

fun up bind arr unzip node mk_zipper zipper =
  let val (next, parent) = unzip zipper
  in
    bind parent
    (arr (fn parent_zipper =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = node content next
      in mk_zipper content zcontext end))
  end

structure Up1 : BI_ZIPPER_MOVE =
struct
  structure ZMB = Zipper_Move_Base(Kleisli(PM1))
  open ZMB
  type ('c1, 'c2) from = ('c1, 'c2) Z1.zipper
  type ('c1, 'c2) to = ('c1, 'c2) Z2.zipper
  structure A = Kleisli_Arrow_Apply(PM1)
  fun move zipper = up PM1.bind A.arr Z1.unzip ALC.N2.N.node Z2.zipper zipper
end

structure Up2 : BI_ZIPPER_MOVE =
struct
  structure ZMB = Zipper_Move_Base(Kleisli(PM2))
  open ZMB
  type ('c1, 'c2) from = ('c1, 'c2) Z2.zipper
  type ('c1, 'c2) to = ('c1, 'c2) Z1.zipper
  structure A = Kleisli_Arrow_Apply(PM2)
  fun move zipper = up PM2.bind A.arr Z2.unzip ALC.N1.N.node Z1.zipper zipper
end

end

functor Test(AZ : ALTERNATING_LINKED_CONTAINERS_ZIPPER) =
struct

fun recurse p plus base next x =
  if p x then base x else plus x (recurse p plus base next (next x))

fun f traverse empty plus null g m x =
  if null x
  then empty
  else plus (traverse g x) (f traverse empty plus null g m (m x))

(*

a -> m a
a -> r -> r
a
r

--> r
--> m a
--> m (r -> r) // map (fold...)
--> fold


*)

fun fold or next act zipper acc =
  let val acc = act zipper acc
  in
    (* Move.M.bind (next zipper) (fn zipper => fold or next act zipper acc)  *)
    next zipper
  end

(* fun finish_node dfs_children move_down move_right node =
  let
    val downsq = Seq.make (fn () => move_down node |> seq_of_opt
      |> Seq.maps dfs_children
      |> Seq.pull)
    val rightsq = Seq.make (fn () => move_right node |> seq_of_opt
      |> Seq.maps (dfs_base finish_node dfs_children move_down move_right)
      |> Seq.pull)
  in finish_node node (Seq.append downsq rightsq) end *)


(* fun dfs_base finish_node dfs_children move_down move_right node =
  let
    val downsq = Seq.make (fn () => move_down node |> seq_of_opt
      |> Seq.maps dfs_children
      |> Seq.pull)
    val rightsq = Seq.make (fn () => move_right node |> seq_of_opt
      |> Seq.maps (dfs_base finish_node dfs_children move_down move_right)
      |> Seq.pull)
  in finish_node node (Seq.append downsq rightsq) end

fun dfs_tac_tree path_tac_tree_zipper = dfs_base (K I) dfs_tree
  move_down_path_tac_tree_zipper move_right_path_tac_tree_zipper path_tac_tree_zipper
and dfs_tree path_tree_zipper = dfs_base Seq.cons dfs_tac_tree
  move_down_path_tree_zipper move_right_path_tree_zipper path_tree_zipper *)



end