(*  Title:      HOCLP/alternating_bi_zippers_bi_nodes.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS =
sig
  structure BZ1 : BI_ZIPPER
  structure BZ2 : BI_ZIPPER

  structure N1 : BI_NODE
  where type ('i, 'a, 'b) next = ('i, ('i, 'b, 'a) BZ2.container) BZ2.Init.mt
  sharing type N1.node = BZ1.content

  structure N2 : BI_NODE
  where type ('i, 'a, 'b) next = ('i, ('i, 'b, 'a) BZ1.container) BZ1.Init.mt
  sharing type N2.node = BZ2.content
end

signature ALTERNATING_BI_ZIPPERS_BI_NODES =
sig
    structure A : ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS
    structure N1 : BI_NODE
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) A.N1.content
    where type ('i, 'a, 'b) next = ('i, 'a, 'b) A.N1.next
    where type ('i, 'a, 'b) node = ('i, 'a, 'b) A.N1.node
    structure N2 : BI_NODE
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) A.N2.content
    where type ('i, 'a, 'b) next = ('i, 'a, 'b) A.N2.next
    where type ('i, 'a, 'b) node = ('i, 'a, 'b) A.N2.node
    structure ZD : ZIPPER_DATA
    structure PM1 : IMONAD_BASE
    structure PM2 : IMONAD_BASE
    type ('i, 'a, 'b) zcontext1
    type ('i, 'a, 'b) zcontext2
    type ('i, 'a, 'b) parent1 = ('i, 'i, (('i, 'b, 'a) N2.content, ('i, 'b, 'a) zcontext2) ZD.zipper) PM1.t
    type ('i, 'a, 'b) parent2 = ('i, 'i, (('i, 'b, 'a) N1.content, ('i, 'b, 'a) zcontext1) ZD.zipper) PM2.t
    val mk_zcontext1 : ('i, 'a, 'b) A.BZ1.zcontext -> ('i, 'a, 'b) parent1 -> ('i, 'a, 'b) zcontext1
    val mk_zcontext2 : ('i, 'a, 'b) A.BZ2.zcontext -> ('i, 'a, 'b) parent2 -> ('i, 'a, 'b) zcontext2
    val parent1 : unit -> (('i, 'a, 'b) zcontext1, ('i, 'a, 'b) parent1,
      ('i, 'a, 'b) zcontext1, ('i, 'a, 'b) parent1) SLens.lens
    val lzcontext1 : unit -> (('i, 'a, 'b) zcontext1, ('i, 'a, 'b) A.BZ1.zcontext,
      ('i, 'a, 'b) zcontext1, ('i, 'a, 'b) A.BZ1.zcontext) SLens.lens
    val parent2 : unit -> (('i, 'a, 'b) zcontext2, ('i, 'a, 'b) parent2,
      ('i, 'a, 'b) zcontext2, ('i, 'a, 'b) parent2) SLens.lens
    val lzcontext2 : unit -> (('i, 'a, 'b) zcontext2, ('i, 'a, 'b) A.BZ2.zcontext,
      ('i, 'a, 'b) zcontext2, ('i, 'a, 'b) A.BZ2.zcontext) SLens.lens

    include ALTERNATING_BI_ZIPPERS
    where type ('i, 'a, 'b) Z1.content = ('i, 'a, 'b) A.BZ1.content
    where type ('i, 'a, 'b) Z1.zcontext = ('i, 'a, 'b) zcontext1
    where type ('i, 'a, 'b) Z1.container = ('i, 'a, 'b) A.BZ1.container * ('i, 'a, 'b) parent1
    where type ('i, 'j, 'a) Z1.K.M.t = ('i, 'j, 'a) A.BZ1.K.M.t
    where type ('i, 'a, 'b) Z2.content = ('i, 'a, 'b) A.BZ2.content
    where type ('i, 'a, 'b) Z2.zcontext = ('i, 'a, 'b) zcontext2
    where type ('i, 'a, 'b) Z2.container = ('i, 'a, 'b) A.BZ2.container * ('i, 'a, 'b) parent2
    where type ('i, 'j, 'a) Z2.K.M.t = ('i, 'j, 'a) A.BZ2.K.M.t
    where type ('i, 'j, 'a) Up1.K.M.t = ('i, 'j, 'a) PM1.t
    where type ('i, 'j, 'a) Up2.K.M.t = ('i, 'j, 'a) PM2.t
end

functor Alternating_Bi_Zippers_Bi_Nodes(
    structure A : ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS
    structure ZD : ZIPPER_DATA
    structure PM1 : IMONAD_BASE
    structure PM2 : IMONAD_BASE
  ) : ALTERNATING_BI_ZIPPERS_BI_NODES =
struct

structure A = A
open A
structure ZD = ZD
structure PM1 = PM1
structure PM2 = PM2

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

type ('i, 'a, 'b) lzcontext1 = ('i, 'a, 'b) BZ1.zcontext
type ('i, 'a, 'b) lzcontext2 = ('i, 'a, 'b) BZ2.zcontext

datatype ('i, 'a, 'b) zcontext1 = ZContext1 of (
    ('i, 'a, 'b) lzcontext1,
    ('i, 'i, (('i, 'b, 'a) N2.content, ('i, 'b, 'a) zcontext2) ZD.zipper) PM1.t
  ) lzcontext_parent
and ('i, 'a, 'b) zcontext2 = ZContext2 of (
    ('i, 'a, 'b) lzcontext2,
    ('i, 'i, (('i, 'b, 'a) N1.content, ('i, 'b, 'a) zcontext1) ZD.zipper) PM2.t
  ) lzcontext_parent

type ('i, 'a, 'b) parent1 = ('i, 'i, (('i, 'b, 'a) N2.content, ('i, 'b, 'a) zcontext2) ZD.zipper) PM1.t
type ('i, 'a, 'b) parent2 = ('i, 'i, (('i, 'b, 'a) N1.content, ('i, 'b, 'a) zcontext1) ZD.zipper) PM2.t

fun mk_zcontext1 lzcontext parent = ZContext1 (lzcontext_parent lzcontext parent)
fun mk_zcontext2 lzcontext parent = ZContext2 (lzcontext_parent lzcontext parent)

fun get_zcontext1_lzcontext (ZContext1 {lzcontext, ...}) = lzcontext
fun get_zcontext1_parent (ZContext1 {parent, ...}) = parent
fun map_zcontext1_lzcontext f (ZContext1 {lzcontext, parent}) =
  (ZContext1 {lzcontext = f lzcontext, parent = parent})
fun map_zcontext1_parent f (ZContext1 {lzcontext, parent}) =
  (ZContext1 {lzcontext = lzcontext, parent = f parent})
fun lzcontext1 _ = SLens.lens get_zcontext1_lzcontext (uncurry map_zcontext1_lzcontext)
fun parent1 _ = SLens.lens get_zcontext1_parent (uncurry map_zcontext1_parent)

fun get_zcontext2_lzcontext (ZContext2 {lzcontext, ...}) = lzcontext
fun get_zcontext2_parent (ZContext2 {parent, ...}) = parent
fun map_zcontext2_lzcontext f (ZContext2 {lzcontext, parent}) =
  (ZContext2 {lzcontext = f lzcontext, parent = parent})
fun map_zcontext2_parent f (ZContext2 {lzcontext, parent}) =
  (ZContext2 {lzcontext = lzcontext, parent = f parent})
fun lzcontext2 _ = SLens.lens get_zcontext2_lzcontext (uncurry map_zcontext2_lzcontext)
fun parent2 _ = SLens.lens get_zcontext2_parent (uncurry map_zcontext2_parent)

structure Z1 = Extend_Bi_Zipper_Context(
  structure ZD = ZD
  structure Z = BZ1
  type ('i, 'a, 'b) new_zcontext = ('i, 'a, 'b) parent1
  type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) zcontext1
  val mk_zcontext = mk_zcontext1
  val get_old_zcontext = get_zcontext1_lzcontext
  val get_new_zcontext = get_zcontext1_parent
)

structure Z2 = Extend_Bi_Zipper_Context(
  structure ZD = ZD
  structure Z = BZ2
  type ('i, 'a, 'b) new_zcontext = ('i, 'a, 'b) parent2
  type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) zcontext2
  val mk_zcontext = mk_zcontext2
  val get_old_zcontext = get_zcontext2_lzcontext
  val get_new_zcontext = get_zcontext2_parent
)

fun down bind arr comp pm_pure get_content get_zcontext dest_node init zipper = zipper |>
  (arr (get_content #> dest_node)
  |> comp (fn {content, next} => bind next
    (fn next_data =>
      let val parent = ZD.zipper content (get_zcontext zipper) |> pm_pure
      in init (next_data, parent) end)))

structure Down1 : BI_MOVE =
struct
  structure MB = Move_Base(Z2.Init.K)
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper
  structure A = IKleisli_IArrow_Apply(MB.K.M)
  open A
  fun move zipper = zipper |>
    down M.bind arr comp PM2.pure Z1.get_content Z1.get_zcontext N1.dest_node Z2.Init.move
end

structure Down2 : BI_MOVE =
struct
  structure MB = Move_Base(Z1.Init.K)
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
  structure A = IKleisli_IArrow_Apply(MB.K.M)
  open A
  fun move zipper = zipper |>
    down M.bind arr comp PM1.pure Z2.get_content Z2.get_zcontext N2.dest_node Z1.Init.move
end

fun up bind arr nm_pure unzip node mk_zipper zipper =
  let val (next, parent) = unzip zipper
  in
    bind parent
    (arr (fn parent_zipper =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = node content (nm_pure next)
      in mk_zipper content zcontext end))
  end

structure Up1 : BI_MOVE =
struct
  structure MB = Move_Base(IKleisli(PM1))
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper
  structure A = IKleisli_IArrow_Apply(PM1)
  fun move zipper = zipper
    |> up PM1.bind A.arr Z1.Init.K.M.pure Z1.unzip N2.node Z2.zipper
end

structure Up2 : BI_MOVE =
struct
  structure MB = Move_Base(IKleisli(PM2))
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
  structure A = IKleisli_IArrow_Apply(PM2)
  fun move zipper = zipper
    |> up PM2.bind A.arr Z2.Init.K.M.pure Z2.unzip N1.node Z1.zipper
end

end
