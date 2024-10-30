(*  Title:      HOCLP/alternating_qzippers_qnodes.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_QZIPPERS_QNODES_BASE_ARGS =
sig
  structure Z1 : QZIPPER
  structure Z2 : QZIPPER
  structure Z3 : QZIPPER
  structure Z4 : QZIPPER

  structure N1 : QNODE
  where type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z2.container) Z2.Init.move
  sharing type N1.node = Z1.content
  structure N2 : QNODE
  where type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z3.container) Z3.Init.move
  sharing type N2.node = Z2.content
  structure N3 : QNODE
  where type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z4.container) Z4.Init.move
  sharing type N3.node = Z3.content
  structure N4 : QNODE
  where type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z1.container) Z1.Init.move
  sharing type N4.node = Z4.content
end

signature ALTERNATING_QZIPPERS_QNODES =
sig
    structure A : ALTERNATING_QZIPPERS_QNODES_BASE_ARGS
    structure N1 : QNODE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) A.N1.content
    where type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) A.N1.next
    where type ('i, 'a, 'b, 'c, 'd) node = ('i, 'a, 'b, 'c, 'd) A.N1.node
    structure N2 : QNODE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) A.N2.content
    where type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) A.N2.next
    where type ('i, 'a, 'b, 'c, 'd) node = ('i, 'a, 'b, 'c, 'd) A.N2.node
    structure N3 : QNODE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) A.N3.content
    where type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) A.N3.next
    where type ('i, 'a, 'b, 'c, 'd) node = ('i, 'a, 'b, 'c, 'd) A.N3.node
    structure N4 : QNODE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) A.N4.content
    where type ('i, 'a, 'b, 'c, 'd) next = ('i, 'a, 'b, 'c, 'd) A.N4.next
    where type ('i, 'a, 'b, 'c, 'd) node = ('i, 'a, 'b, 'c, 'd) A.N4.node

    structure ZD : ZIPPER_DATA
    structure UMB1 : MOVE_BASE
    structure UMB2 : MOVE_BASE
    structure UMB3 : MOVE_BASE
    structure UMB4 : MOVE_BASE

    type ('i, 'a, 'b, 'c, 'd) zcontext1
    type ('i, 'a, 'b, 'c, 'd) zcontext2
    type ('i, 'a, 'b, 'c, 'd) zcontext3
    type ('i, 'a, 'b, 'c, 'd) zcontext4
    type ('i, 'a, 'b, 'c, 'd) parent1 = ('i, unit, (('i, 'd, 'a, 'b, 'c) N4.content,
      ('i, 'd, 'a, 'b, 'c) zcontext4) ZD.zipper) UMB1.move
    type ('i, 'a, 'b, 'c, 'd) parent2 = ('i, unit, (('i, 'd, 'a, 'b, 'c) N1.content,
      ('i, 'd, 'a, 'b, 'c) zcontext1) ZD.zipper) UMB2.move
    type ('i, 'a, 'b, 'c, 'd) parent3 = ('i, unit, (('i, 'd, 'a, 'b, 'c) N2.content,
      ('i, 'd, 'a, 'b, 'c) zcontext2) ZD.zipper) UMB3.move
    type ('i, 'a, 'b, 'c, 'd) parent4 = ('i, unit, (('i, 'd, 'a, 'b, 'c) N3.content,
      ('i, 'd, 'a, 'b, 'c) zcontext3) ZD.zipper) UMB4.move

    val mk_zcontext1 : ('i, 'a, 'b, 'c, 'd) A.Z1.zcontext -> ('i, 'a, 'b, 'c, 'd) parent1 ->
      ('i, 'a, 'b, 'c, 'd) zcontext1
    val mk_zcontext2 : ('i, 'a, 'b, 'c, 'd) A.Z2.zcontext -> ('i, 'a, 'b, 'c, 'd) parent2 ->
      ('i, 'a, 'b, 'c, 'd) zcontext2
    val mk_zcontext3 : ('i, 'a, 'b, 'c, 'd) A.Z3.zcontext -> ('i, 'a, 'b, 'c, 'd) parent3 ->
      ('i, 'a, 'b, 'c, 'd) zcontext3
    val mk_zcontext4 : ('i, 'a, 'b, 'c, 'd) A.Z4.zcontext -> ('i, 'a, 'b, 'c, 'd) parent4 ->
      ('i, 'a, 'b, 'c, 'd) zcontext4

    val parent1 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext1, ('i, 'a, 'b, 'c, 'd) parent1,
      ('i, 'a, 'b, 'c, 'd) zcontext1, ('i, 'a, 'b, 'c, 'd) parent1) SLens.lens
    val lzcontext1 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext1, ('i, 'a, 'b, 'c, 'd) A.Z1.zcontext,
      ('i, 'a, 'b, 'c, 'd) zcontext1, ('i, 'a, 'b, 'c, 'd) A.Z1.zcontext) SLens.lens
    val parent2 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext2, ('i, 'a, 'b, 'c, 'd) parent2,
      ('i, 'a, 'b, 'c, 'd) zcontext2, ('i, 'a, 'b, 'c, 'd) parent2) SLens.lens
    val lzcontext2 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext2, ('i, 'a, 'b, 'c, 'd) A.Z2.zcontext,
      ('i, 'a, 'b, 'c, 'd) zcontext2, ('i, 'a, 'b, 'c, 'd) A.Z2.zcontext) SLens.lens
    val parent3 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext3, ('i, 'a, 'b, 'c, 'd) parent3,
      ('i, 'a, 'b, 'c, 'd) zcontext3, ('i, 'a, 'b, 'c, 'd) parent3) SLens.lens
    val lzcontext3 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext3, ('i, 'a, 'b, 'c, 'd) A.Z3.zcontext,
      ('i, 'a, 'b, 'c, 'd) zcontext3, ('i, 'a, 'b, 'c, 'd) A.Z3.zcontext) SLens.lens
    val parent4 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext4, ('i, 'a, 'b, 'c, 'd) parent4,
      ('i, 'a, 'b, 'c, 'd) zcontext4, ('i, 'a, 'b, 'c, 'd) parent4) SLens.lens
    val lzcontext4 : unit -> (('i, 'a, 'b, 'c, 'd) zcontext4, ('i, 'a, 'b, 'c, 'd) A.Z4.zcontext,
      ('i, 'a, 'b, 'c, 'd) zcontext4, ('i, 'a, 'b, 'c, 'd) A.Z4.zcontext) SLens.lens

    include ALTERNATING_QZIPPERS
    where type ('i, 'a, 'b, 'c, 'd) Z1.content = ('i, 'a, 'b, 'c, 'd) A.Z1.content
    where type ('i, 'a, 'b, 'c, 'd) Z1.zcontext = ('i, 'a, 'b, 'c, 'd) zcontext1
    where type ('i, 'a, 'b, 'c, 'd) Z1.container =
      ('i, 'a, 'b, 'c, 'd) A.Z1.container * ('i, 'a, 'b, 'c, 'd) parent1
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) A.Z1.cat
    where type ('i, 'a, 'b, 'c, 'd) Z2.content = ('i, 'a, 'b, 'c, 'd) A.Z2.content
    where type ('i, 'a, 'b, 'c, 'd) Z2.zcontext = ('i, 'a, 'b, 'c, 'd) zcontext2
    where type ('i, 'a, 'b, 'c, 'd) Z2.container =
      ('i, 'a, 'b, 'c, 'd) A.Z2.container * ('i, 'a, 'b, 'c, 'd) parent2
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) A.Z2.cat
    where type ('i, 'a, 'b, 'c, 'd) Z3.content = ('i, 'a, 'b, 'c, 'd) A.Z3.content
    where type ('i, 'a, 'b, 'c, 'd) Z3.zcontext = ('i, 'a, 'b, 'c, 'd) zcontext3
    where type ('i, 'a, 'b, 'c, 'd) Z3.container =
      ('i, 'a, 'b, 'c, 'd) A.Z3.container * ('i, 'a, 'b, 'c, 'd) parent3
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) A.Z3.cat
    where type ('i, 'a, 'b, 'c, 'd) Z4.content = ('i, 'a, 'b, 'c, 'd) A.Z4.content
    where type ('i, 'a, 'b, 'c, 'd) Z4.zcontext = ('i, 'a, 'b, 'c, 'd) zcontext4
    where type ('i, 'a, 'b, 'c, 'd) Z4.container =
      ('i, 'a, 'b, 'c, 'd) A.Z4.container * ('i, 'a, 'b, 'c, 'd) parent4
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) A.Z4.cat
    where type ('i, 'j, 'a, 'b) Up1.cat = ('i, 'j, 'a, 'b) UMB1.cat
    where type ('i, 'j, 'a, 'b) Up2.cat = ('i, 'j, 'a, 'b) UMB2.cat
    where type ('i, 'j, 'a, 'b) Up3.cat = ('i, 'j, 'a, 'b) UMB3.cat
    where type ('i, 'j, 'a, 'b) Up4.cat = ('i, 'j, 'a, 'b) UMB4.cat
end

signature LAZY_IARROW_IARROW_APPLY_BASE =
sig
  structure A : LAZY_IARROW
  structure AA : LAZY_IARROW_APPLY_BASE
  sharing type A.T.cat = AA.T.cat
end

functor Alternating_QZippers_QNodes(
    structure DA1 : LAZY_IARROW_IARROW_APPLY_BASE
    structure DA2 : LAZY_IARROW_IARROW_APPLY_BASE
    structure DA3 : LAZY_IARROW_IARROW_APPLY_BASE
    structure DA4 : LAZY_IARROW_IARROW_APPLY_BASE
    structure UA1 : LAZY_IARROW_IARROW_APPLY_BASE
    structure UA2 : LAZY_IARROW_IARROW_APPLY_BASE
    structure UA3 : LAZY_IARROW_IARROW_APPLY_BASE
    structure UA4 : LAZY_IARROW_IARROW_APPLY_BASE
    structure A : ALTERNATING_QZIPPERS_QNODES_BASE_ARGS
    where type ('i, 'j, 'a, 'b) Z1.cat = ('i, 'j, 'a, 'b) DA4.A.cat
    where type ('i, 'j, 'a, 'b) Z2.cat = ('i, 'j, 'a, 'b) DA1.A.cat
    where type ('i, 'j, 'a, 'b) Z3.cat = ('i, 'j, 'a, 'b) DA2.A.cat
    where type ('i, 'j, 'a, 'b) Z4.cat = ('i, 'j, 'a, 'b) DA3.A.cat
    structure ZD : ZIPPER_DATA
  ) : ALTERNATING_QZIPPERS_QNODES =
struct

structure A = A
open A
structure ZD = ZD
structure UMB1 = Move_Base(UA1.AA)
structure UMB2 = Move_Base(UA2.AA)
structure UMB3 = Move_Base(UA3.AA)
structure UMB4 = Move_Base(UA4.AA)

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

type ('i, 'a, 'b, 'c, 'd) lzcontext1 = ('i, 'a, 'b, 'c, 'd) Z1.zcontext
type ('i, 'a, 'b, 'c, 'd) lzcontext2 = ('i, 'a, 'b, 'c, 'd) Z2.zcontext
type ('i, 'a, 'b, 'c, 'd) lzcontext3 = ('i, 'a, 'b, 'c, 'd) Z3.zcontext
type ('i, 'a, 'b, 'c, 'd) lzcontext4 = ('i, 'a, 'b, 'c, 'd) Z4.zcontext

datatype ('i, 'a, 'b, 'c, 'd) zcontext1 = ZContext1 of (
    ('i, 'a, 'b, 'c, 'd) lzcontext1,
    ('i, unit, (('i, 'd, 'a, 'b, 'c) N4.content, ('i, 'd, 'a, 'b, 'c) zcontext4) ZD.zipper) UMB1.move
  ) lzcontext_parent
and ('i, 'a, 'b, 'c, 'd) zcontext2 = ZContext2 of (
    ('i, 'a, 'b, 'c, 'd) lzcontext2,
    ('i, unit, (('i, 'd, 'a, 'b, 'c) N1.content, ('i, 'd, 'a, 'b, 'c) zcontext1) ZD.zipper) UMB2.move
  ) lzcontext_parent
and ('i, 'a, 'b, 'c, 'd) zcontext3 = ZContext3 of (
    ('i, 'a, 'b, 'c, 'd) lzcontext3,
    ('i, unit, (('i, 'd, 'a, 'b, 'c) N2.content, ('i, 'd, 'a, 'b, 'c) zcontext2) ZD.zipper) UMB3.move
  ) lzcontext_parent
and ('i, 'a, 'b, 'c, 'd) zcontext4 = ZContext4 of (
    ('i, 'a, 'b, 'c, 'd) lzcontext4,
    ('i, unit, (('i, 'd, 'a, 'b, 'c) N3.content, ('i, 'd, 'a, 'b, 'c) zcontext3) ZD.zipper) UMB4.move
  ) lzcontext_parent

type ('i, 'a, 'b, 'c, 'd) parent1 =
  ('i, unit, (('i, 'd, 'a, 'b, 'c) N4.content, ('i, 'd, 'a, 'b, 'c) zcontext4) ZD.zipper) UMB1.move
type ('i, 'a, 'b, 'c, 'd) parent2 =
  ('i, unit, (('i, 'd, 'a, 'b, 'c) N1.content, ('i, 'd, 'a, 'b, 'c) zcontext1) ZD.zipper) UMB2.move
type ('i, 'a, 'b, 'c, 'd) parent3 =
  ('i, unit, (('i, 'd, 'a, 'b, 'c) N2.content, ('i, 'd, 'a, 'b, 'c) zcontext2) ZD.zipper) UMB3.move
type ('i, 'a, 'b, 'c, 'd) parent4 =
  ('i, unit, (('i, 'd, 'a, 'b, 'c) N3.content, ('i, 'd, 'a, 'b, 'c) zcontext3) ZD.zipper) UMB4.move

fun mk_zcontext1 lzcontext parent = ZContext1 (lzcontext_parent lzcontext parent)
fun mk_zcontext2 lzcontext parent = ZContext2 (lzcontext_parent lzcontext parent)
fun mk_zcontext3 lzcontext parent = ZContext3 (lzcontext_parent lzcontext parent)
fun mk_zcontext4 lzcontext parent = ZContext4 (lzcontext_parent lzcontext parent)

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

fun get_zcontext3_lzcontext (ZContext3 {lzcontext, ...}) = lzcontext
fun get_zcontext3_parent (ZContext3 {parent, ...}) = parent
fun map_zcontext3_lzcontext f (ZContext3 {lzcontext, parent}) =
  (ZContext3 {lzcontext = f lzcontext, parent = parent})
fun map_zcontext3_parent f (ZContext3 {lzcontext, parent}) =
  (ZContext3 {lzcontext = lzcontext, parent = f parent})
fun lzcontext3 _ = SLens.lens get_zcontext3_lzcontext (uncurry map_zcontext3_lzcontext)
fun parent3 _ = SLens.lens get_zcontext3_parent (uncurry map_zcontext3_parent)

fun get_zcontext4_lzcontext (ZContext4 {lzcontext, ...}) = lzcontext
fun get_zcontext4_parent (ZContext4 {parent, ...}) = parent
fun map_zcontext4_lzcontext f (ZContext4 {lzcontext, parent}) =
  (ZContext4 {lzcontext = f lzcontext, parent = parent})
fun map_zcontext4_parent f (ZContext4 {lzcontext, parent}) =
  (ZContext4 {lzcontext = lzcontext, parent = f parent})
fun lzcontext4 _ = SLens.lens get_zcontext4_lzcontext (uncurry map_zcontext4_lzcontext)
fun parent4 _ = SLens.lens get_zcontext4_parent (uncurry map_zcontext4_parent)

structure Z1 = Extend_QZipper_Context(
  structure Z = A.Z1
  structure A = DA4.A
  structure ZD = ZD
  type ('i, 'a, 'b, 'c, 'd) new_zcontext = ('i, 'a, 'b, 'c, 'd) parent1
  type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) zcontext1
  val mk_zcontext = mk_zcontext1
  val get_old_zcontext = get_zcontext1_lzcontext
  val get_new_zcontext = get_zcontext1_parent
)

structure Z2 = Extend_QZipper_Context(
  structure Z = A.Z2
  structure A = DA1.A
  structure ZD = ZD
  type ('i, 'a, 'b, 'c, 'd) new_zcontext = ('i, 'a, 'b, 'c, 'd) parent2
  type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) zcontext2
  val mk_zcontext = mk_zcontext2
  val get_old_zcontext = get_zcontext2_lzcontext
  val get_new_zcontext = get_zcontext2_parent
)

structure Z3 = Extend_QZipper_Context(
  structure Z = A.Z3
  structure A = DA2.A
  structure ZD = ZD
  type ('i, 'a, 'b, 'c, 'd) new_zcontext = ('i, 'a, 'b, 'c, 'd) parent3
  type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) zcontext3
  val mk_zcontext = mk_zcontext3
  val get_old_zcontext = get_zcontext3_lzcontext
  val get_new_zcontext = get_zcontext3_parent
)

structure Z4 = Extend_QZipper_Context(
  structure Z = A.Z4
  structure A = DA3.A
  structure ZD = ZD
  type ('i, 'a, 'b, 'c, 'd) new_zcontext = ('i, 'a, 'b, 'c, 'd) parent4
  type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) zcontext4
  val mk_zcontext = mk_zcontext4
  val get_old_zcontext = get_zcontext4_lzcontext
  val get_new_zcontext = get_zcontext4_parent
)

structure Down1 : QMOVE =
struct
  structure MB : MOVE_BASE = Z2.Init
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z1.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z2.zipper
  structure SC = ISemi_Category(DA1.A) open SC DA1
  fun move _ =
    (A.arr (fn zipper =>
      Z1.get_content zipper |> N1.dest_node |> (fn {content, next} => ((next, ()), (zipper, content))))
    >>> A.***
      (AA.app, A.arr (fn (zipper, content) => ZD.zipper content (Z1.get_zcontext zipper) |> UA2.A.K))
    >>> Z2.Init.move)
    ()
end

structure Down2 : QMOVE =
struct
  structure MB : MOVE_BASE = Z3.Init
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z2.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z3.zipper
  structure SC = ISemi_Category(DA2.A) open SC DA2
  fun move _ =
    (A.arr (fn zipper =>
      Z2.get_content zipper |> N2.dest_node |> (fn {content, next} => ((next, ()), (zipper, content))))
    >>> A.***
      (AA.app, A.arr (fn (zipper, content) => ZD.zipper content (Z2.get_zcontext zipper) |> UA3.A.K))
    >>> Z3.Init.move)
    ()
end

structure Down3 : QMOVE =
struct
  structure MB : MOVE_BASE = Z4.Init
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z3.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z4.zipper
  structure SC = ISemi_Category(DA3.A) open SC DA3
  fun move _ =
    (A.arr (fn zipper =>
      Z3.get_content zipper |> N3.dest_node |> (fn {content, next} => ((next, ()), (zipper, content))))
    >>> A.***
      (AA.app, A.arr (fn (zipper, content) => ZD.zipper content (Z3.get_zcontext zipper) |> UA4.A.K))
    >>> Z4.Init.move)
    ()
end

structure Down4 : QMOVE =
struct
  structure MB : MOVE_BASE = Z1.Init
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z4.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'b, 'c, 'd, 'a) Z1.zipper
  structure SC = ISemi_Category(DA4.A) open SC DA4
  fun move _ =
    (A.arr (fn zipper =>
      Z4.get_content zipper |> N4.dest_node |> (fn {content, next} => ((next, ()), (zipper, content))))
    >>> A.***
      (AA.app, A.arr (fn (zipper, content) => ZD.zipper content (Z4.get_zcontext zipper) |> UA1.A.K))
    >>> Z1.Init.move)
    ()
end

structure Up1 : QMOVE =
struct
  structure MB = UMB1
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z1.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z4.zipper
  structure SC = ISemi_Category(MB) open SC UA1
  fun move _ = (A.arr (Z1.unzip #> apsnd (rpair ()))
    >>> A.second AA.app
    >>> A.arr (fn (next, parent_zipper) =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = N4.node content (DA4.A.K next)
      in Z4.zipper content zcontext end))
    ()
end

structure Up2 : QMOVE =
struct
  structure MB = UMB2
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z2.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z1.zipper
  structure SC = ISemi_Category(MB) open SC UA2
  fun move _ = (A.arr (Z2.unzip #> apsnd (rpair ()))
    >>> A.second AA.app
    >>> A.arr (fn (next, parent_zipper) =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = N1.node content (DA1.A.K next)
      in Z1.zipper content zcontext end))
    ()
end

structure Up3 : QMOVE =
struct
  structure MB = UMB3
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z3.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z2.zipper
  structure SC = ISemi_Category(MB) open SC UA3
  fun move _ = (A.arr (Z3.unzip #> apsnd (rpair ()))
    >>> A.second AA.app
    >>> A.arr (fn (next, parent_zipper) =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = N2.node content (DA2.A.K next)
      in Z2.zipper content zcontext end))
    ()
end

structure Up4 : QMOVE =
struct
  structure MB = UMB4
  open MB
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) Z4.zipper
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'd, 'a, 'b, 'c) Z3.zipper
  structure SC = ISemi_Category(MB) open SC UA4
  fun move _ = (A.arr (Z4.unzip #> apsnd (rpair ()))
    >>> A.second AA.app
    >>> A.arr (fn (next, parent_zipper) =>
      let
        val {content, zcontext} = ZD.dest_zipper parent_zipper
        val content = N3.node content (DA3.A.K next)
      in Z3.zipper content zcontext end))
    ()
end

end
