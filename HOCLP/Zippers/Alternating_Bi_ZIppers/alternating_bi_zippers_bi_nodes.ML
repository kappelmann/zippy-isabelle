(*  Title:      HOCLP/alternating_bi_zippers_bi_nodes.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS =
sig
  structure BZ1 : BI_ZIPPER
  structure BZ2 : BI_ZIPPER

  structure N1 : BI_NODE
  where type ('i, 'a, 'b) next = ('i, unit, ('i, 'b, 'a) BZ2.container) BZ2.Init.move
  sharing type N1.node = BZ1.content

  structure N2 : BI_NODE
  where type ('i, 'a, 'b) next = ('i, unit, ('i, 'b, 'a) BZ1.container) BZ1.Init.move
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
    structure DA1 : IARROW_APPLY_BASE
    structure DA2 : IARROW_APPLY_BASE
    structure UA1 : IARROW_APPLY_BASE
    structure UA2 : IARROW_APPLY_BASE
    type ('i, 'a, 'b) zcontext1
    type ('i, 'a, 'b) zcontext2
    type ('i, 'a, 'b) parent1 =
      ('i, 'i, unit, (('i, 'b, 'a) N2.content, ('i, 'b, 'a) zcontext2) ZD.zipper) UA1.cat
    type ('i, 'a, 'b) parent2 =
      ('i, 'i, unit, (('i, 'b, 'a) N1.content, ('i, 'b, 'a) zcontext1) ZD.zipper) UA2.cat
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
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) A.BZ1.cat
    where type ('i, 'a, 'b) Z2.content = ('i, 'a, 'b) A.BZ2.content
    where type ('i, 'a, 'b) Z2.zcontext = ('i, 'a, 'b) zcontext2
    where type ('i, 'a, 'b) Z2.container = ('i, 'a, 'b) A.BZ2.container * ('i, 'a, 'b) parent2
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) A.BZ2.cat
    where type ('i, 'j, 'a, 'b) Down1.cat = ('i, 'j, 'a, 'b) DA1.cat
    where type ('i, 'j, 'a, 'b) Down2.cat = ('i, 'j, 'a, 'b) DA2.cat
    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) UA1.cat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) UA2.cat
end

signature LAZY_IARROW_IARROW_APPLY_BASE =
sig
  structure A : LAZY_IARROW
  structure AA : LAZY_IARROW_APPLY_BASE
  sharing type A.T.cat = AA.T.cat
end

functor Alternating_Bi_Zippers_Bi_Nodes(
    structure UA1 : LAZY_IARROW_IARROW_APPLY_BASE
    structure UA2 : LAZY_IARROW_IARROW_APPLY_BASE
    structure DA1 : LAZY_IARROW_IARROW_APPLY_BASE
    structure DA2 : LAZY_IARROW_IARROW_APPLY_BASE
    structure A : ALTERNATING_BI_ZIPPERS_BI_NODES_BASE_ARGS
    where type ('i, 'j, 'a, 'b) BZ1.cat = ('i, 'j, 'a, 'b) DA2.A.cat
    where type ('i, 'j, 'a, 'b) BZ2.cat = ('i, 'j, 'a, 'b) DA1.A.cat
    structure ZD : ZIPPER_DATA
  ) : ALTERNATING_BI_ZIPPERS_BI_NODES =
(* )= *)
struct

structure A = A
open A
structure ZD = ZD
structure DA1in = DA1
structure DA2in = DA2
structure UA1in = UA1
structure UA2in = UA2
structure DA1 = DA1.AA
structure DA2 = DA2.AA
structure UA1 = UA1.AA
structure UA2 = UA2.AA

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
    ('i, 'i, unit, (('i, 'b, 'a) N2.content, ('i, 'b, 'a) zcontext2) ZD.zipper) UA1.cat
  ) lzcontext_parent
and ('i, 'a, 'b) zcontext2 = ZContext2 of (
    ('i, 'a, 'b) lzcontext2,
    ('i, 'i, unit, (('i, 'b, 'a) N1.content, ('i, 'b, 'a) zcontext1) ZD.zipper) UA2.cat
  ) lzcontext_parent

type ('i, 'a, 'b) parent1 =
  ('i, 'i, unit, (('i, 'b, 'a) N2.content, ('i, 'b, 'a) zcontext2) ZD.zipper) UA1.cat
type ('i, 'a, 'b) parent2 =
  ('i, 'i, unit, (('i, 'b, 'a) N1.content, ('i, 'b, 'a) zcontext1) ZD.zipper) UA2.cat

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
  structure A = DA2in.A
  structure ZD = ZD
  structure Z = BZ1
  type ('i, 'a, 'b) new_zcontext = ('i, 'a, 'b) parent1
  type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) zcontext1
  val mk_zcontext = mk_zcontext1
  val get_old_zcontext = get_zcontext1_lzcontext
  val get_new_zcontext = get_zcontext1_parent
)

structure Z2 = Extend_Bi_Zipper_Context(
  structure A = DA1in.A
  structure ZD = ZD
  structure Z = BZ2
  type ('i, 'a, 'b) new_zcontext = ('i, 'a, 'b) parent2
  type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) zcontext2
  val mk_zcontext = mk_zcontext2
  val get_old_zcontext = get_zcontext2_lzcontext
  val get_new_zcontext = get_zcontext2_parent
)

structure Down1 : BI_MOVE =
struct
  structure MB : MOVE_BASE = Z2.Init
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper
  structure SC = ISemi_Category(DA1) open SC DA1in
  fun move _ =
    (A.arr (fn zipper =>
      Z1.get_content zipper |> N1.dest_node |> (fn {content, next} => ((next, ()), (zipper, content))))
    >>> A.***
      (AA.app, A.arr (fn (zipper, content) => ZD.zipper content (Z1.get_zcontext zipper) |> UA2in.A.K))
    >>> Z2.Init.move)
    ()
end

structure Down2 : BI_MOVE =
struct
  structure MB : MOVE_BASE = Z1.Init
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
  structure SC = ISemi_Category(DA2) open SC DA2in
  fun move _ =
    (A.arr (fn zipper =>
      Z2.get_content zipper |> N2.dest_node |> (fn {content, next} => ((next, ()), (zipper, content))))
    >>> A.***
      (AA.app, A.arr (fn (zipper, content) => ZD.zipper content (Z2.get_zcontext zipper) |> UA1in.A.K))
    >>> Z1.Init.move)
    ()
end

structure Up1 : BI_MOVE =
struct
  structure MB = Move_Base(UA1)
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper
  structure SC = ISemi_Category(MB) open SC UA1in
  fun move _ = (A.arr (Z1.unzip #> apsnd (rpair ()))
    >>> A.second AA.app
    >>> A.arr (fn (next, parent_zipper) =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = N2.node content (DA2in.A.K next)
      in Z2.zipper content zcontext end))
    ()
end

structure Up2 : BI_MOVE =
struct
  structure MB = Move_Base(UA2)
  open MB
  type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
  structure SC = ISemi_Category(MB) open SC UA2in
  fun move _ = (A.arr (Z2.unzip #> apsnd (rpair ()))
    >>> A.second AA.app
    >>> A.arr (fn (next, parent_zipper) =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = N1.node content (DA1in.A.K next)
      in Z1.zipper content zcontext end))
    ()
end

end
