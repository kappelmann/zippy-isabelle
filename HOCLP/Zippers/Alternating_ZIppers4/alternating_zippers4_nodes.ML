(*  Title:      HOCLP/alternating_zippers4_nodes.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_ZIPPERS4_NODES_BASE_ARGS =
sig
  structure Z1 : ZIPPER4
  structure Z2 : ZIPPER4
  sharing type Z2.cat = Z1.cat
  sharing type Z2.ZO.L.lens = Z1.ZO.L.lens
  structure Z3 : ZIPPER4
  sharing type Z3.cat = Z1.cat
  sharing type Z3.ZO.L.lens = Z1.ZO.L.lens
  structure Z4 : ZIPPER4
  sharing type Z4.cat = Z1.cat
  sharing type Z4.ZO.L.lens = Z1.ZO.L.lens

  structure N1 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container) Z2.move
  sharing type N1.node = Z1.ZO.content
  sharing type N1.L.C.cat = Z1.cat
  sharing type N1.L.lens = Z1.ZO.L.lens
  structure N2 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container) Z3.move
  sharing type N2.node = Z2.ZO.content
  sharing type N2.L.C.cat = Z2.cat
  sharing type N2.L.lens = Z2.ZO.L.lens
  structure N3 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container) Z4.move
  sharing type N3.node = Z3.ZO.content
  sharing type N3.L.C.cat = Z3.cat
  sharing type N3.L.lens = Z3.ZO.L.lens
  structure N4 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container) Z1.move
  sharing type N4.node = Z4.ZO.content
  sharing type N4.L.C.cat = Z4.cat
  sharing type N4.L.lens = Z4.ZO.L.lens
end

signature ALTERNATING_ZIPPERS4_NODES =
sig
  structure A : ALTERNATING_ZIPPERS4_NODES_BASE_ARGS
  structure N1 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) A.N1.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) A.N1.next
  where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) A.N1.node
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.N1.L.C.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.N1.L.lens
  structure N2 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) A.N2.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) A.N2.next
  where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) A.N2.node
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.N2.L.C.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.N2.L.lens
  structure N3 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) A.N3.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) A.N3.next
  where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) A.N3.node
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.N3.L.C.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.N3.L.lens
  structure N4 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) A.N4.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next = ('p1, 'a1, 'a2, 'a3, 'a4) A.N4.next
  where type ('p1, 'a1, 'a2, 'a3, 'a4) node = ('p1, 'a1, 'a2, 'a3, 'a4) A.N4.node
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.N4.L.C.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.N4.L.lens

  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4
  type ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1
  type ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2
  type ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3
  type ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent1 =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) A.Z1.move
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent2 =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) A.Z2.move
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent3 =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) A.Z3.move
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent4 =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) A.Z4.move

  val mk_zcontext1 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z1.ZO.zcontext *
    ('p1, 'a1, 'a2, 'a3, 'a4) parent1, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1) A.Z1.cat
  val mk_zcontext2 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z2.ZO.zcontext *
    ('p1, 'a1, 'a2, 'a3, 'a4) parent2, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2) A.Z2.cat
  val mk_zcontext3 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z3.ZO.zcontext *
    ('p1, 'a1, 'a2, 'a3, 'a4) parent3, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3) A.Z3.cat
  val mk_zcontext4 : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z4.ZO.zcontext *
    ('p1, 'a1, 'a2, 'a3, 'a4) parent4, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4) A.Z4.cat

  val parent1 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1, ('p1, 'a1, 'a2, 'a3, 'a4) parent1) A.Z1.ZO.L.slens
  val pzipper1 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) A.Z1.ZO.L.slens
  val lzcontext1 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z1.ZO.zcontext) A.Z1.ZO.L.slens
  val parent2 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2, ('p1, 'a1, 'a2, 'a3, 'a4) parent2) A.Z2.ZO.L.slens
  val pzipper2 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) A.Z2.ZO.L.slens
  val lzcontext2 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z2.ZO.zcontext) A.Z2.ZO.L.slens
  val parent3 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3, ('p1, 'a1, 'a2, 'a3, 'a4) parent3) A.Z3.ZO.L.slens
  val pzipper3 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) A.Z3.ZO.L.slens
  val lzcontext3 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z3.ZO.zcontext) A.Z3.ZO.L.slens
  val parent4 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4, ('p1, 'a1, 'a2, 'a3, 'a4) parent4) A.Z4.ZO.L.slens
  val pzipper4 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) A.Z4.ZO.L.slens
  val lzcontext4 : unit -> ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4, ('p1, 'a1, 'a2, 'a3, 'a4) A.Z4.ZO.zcontext) A.Z4.ZO.L.slens

  structure PZO1 : ZIPPER4_OPTICS
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N4.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.Z1.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z1.ZO.L.lens
  structure PZO2 : ZIPPER4_OPTICS
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N1.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.Z2.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z2.ZO.L.lens
  structure PZO3 : ZIPPER4_OPTICS
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N2.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.Z3.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z3.ZO.L.lens
  structure PZO4 : ZIPPER4_OPTICS
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N3.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.Z4.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z4.ZO.L.lens

  include ALTERNATING_ZIPPERS4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) A.Z1.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) A.Z1.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) parent1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) A.Z2.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) A.Z2.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) parent2
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) A.Z3.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) A.Z3.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) parent3
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content = ('p1, 'a1, 'a2, 'a3, 'a4) A.Z4.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) A.Z4.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) parent4
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.Z1.cat
end

functor Alternating_Zippers4_Nodes(
    structure AA : LAZY_ARROW_ARROW_APPLY
    structure A : ALTERNATING_ZIPPERS4_NODES_BASE_ARGS
    where type ('p1, 'a, 'b) Z1.cat = ('p1, 'a, 'b) AA.A.cat
    structure ZD : ZIPPER_DATA
  ) : ALTERNATING_ZIPPERS4_NODES =
struct

structure A = A
open A
structure M : MOVE_BASE = Z1
open M
structure L = Lens_App(open AA; structure L = Z1.ZO.L)

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

type ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext1 = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext
type ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext2 = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext
type ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext3 = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.zcontext
type ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext4 = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.zcontext

datatype ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1 = ZContext1 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext1,
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) move
  ) lzcontext_parent
and ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2 = ZContext2 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext2,
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) move
  ) lzcontext_parent
and ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3 = ZContext3 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext3,
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) move
  ) lzcontext_parent
and ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4 = ZContext4 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext4,
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) move
  ) lzcontext_parent
withtype ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N4.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4) ZD.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N1.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1) ZD.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N2.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2) ZD.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N3.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3) ZD.zipper

type ('p1, 'a1, 'a2, 'a3, 'a4) parent1 = ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) Z1.move
type ('p1, 'a1, 'a2, 'a3, 'a4) parent2 = ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) Z2.move
type ('p1, 'a1, 'a2, 'a3, 'a4) parent3 = ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) Z3.move
type ('p1, 'a1, 'a2, 'a3, 'a4) parent4 = ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) Z4.move

structure Base = struct structure A = AA.A; structure L = L; structure ZD = ZD end
structure PZO1 = Zipper4_Optics_Zipper_Data(
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N4.content
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4
)
structure PZO2 = Zipper4_Optics_Zipper_Data(
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N1.content
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1
)
structure PZO3 = Zipper4_Optics_Zipper_Data(
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N2.content
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2
)
structure PZO4 = Zipper4_Optics_Zipper_Data(
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) N3.content
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3
)


local structure SC = Semi_Category(AA.A); open SC AA.A
in
fun mk_zcontext1 _ = arr (uncurry lzcontext_parent #> ZContext1)
  |> Lazy_Cat_Util.unlift
fun mk_zcontext2 _ = arr (uncurry lzcontext_parent #> ZContext2)
  |> Lazy_Cat_Util.unlift
fun mk_zcontext3 _ = arr (uncurry lzcontext_parent #> ZContext3)
  |> Lazy_Cat_Util.unlift
fun mk_zcontext4 _ = arr (uncurry lzcontext_parent #> ZContext4)
  |> Lazy_Cat_Util.unlift

fun zcontext1 _ = L.lens_get_mk
  (arr (fn (ZContext1 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext1
fun lzcontext1 _ = L.lens_fst (zcontext1 ())
fun parent1 _ = L.lens_snd (zcontext1 ())
fun pzipper1 _ = L.lens_app_K () (parent1 ())

fun zcontext2 _ = L.lens_get_mk
  (arr (fn (ZContext2 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext2
fun lzcontext2 _ = L.lens_fst (zcontext2 ())
fun parent2 _ = L.lens_snd (zcontext2 ())
fun pzipper2 _ = L.lens_app_K () (parent2 ())

fun zcontext3 _ = L.lens_get_mk
  (arr (fn (ZContext3 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext3
fun lzcontext3 _ = L.lens_fst (zcontext3 ())
fun parent3 _ = L.lens_snd (zcontext3 ())
fun pzipper3 _ = L.lens_app_K () (parent3 ())

fun zcontext4 _ = L.lens_get_mk
  (arr (fn (ZContext4 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext4
fun lzcontext4 _ = L.lens_fst (zcontext4 ())
fun parent4 _ = L.lens_snd (zcontext4 ())
fun pzipper4 _ = L.lens_app_K () (parent4 ())

end

structure Base = struct structure A = AA.A; open A end
structure BaseZO = struct structure A = AA.A; structure ZD = ZD; structure L = Z1.ZO.L end
structure Z1 = Extend_Zipper4_Context(
  open Base
  structure Z = Z1
  structure ZO = Zipper4_Optics_Zipper_Data(
    open BaseZO
    type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1
  )
  type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) parent1
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1
  val mk_zcontext = mk_zcontext1
  fun get_base_zcontext _ = L.get (lzcontext1 ())
    |> Lazy_Cat_Util.unlift
  fun get_new_zcontext _ = L.get (parent1 ())
    |> Lazy_Cat_Util.unlift
)
structure Z2 = Extend_Zipper4_Context(
  open Base
  structure Z = Z2
  structure ZO = Zipper4_Optics_Zipper_Data(
    open BaseZO
    type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2
  )
  type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) parent2
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2
  val mk_zcontext = mk_zcontext2
  fun get_base_zcontext _ = L.get (lzcontext2 ())
    |> Lazy_Cat_Util.unlift
  fun get_new_zcontext _ = L.get (parent2 ())
    |> Lazy_Cat_Util.unlift
)
structure Z3 = Extend_Zipper4_Context(
  open Base
  structure Z = Z3
  structure ZO = Zipper4_Optics_Zipper_Data(
    open BaseZO
    type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3
  )
  type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) parent3
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3
  val mk_zcontext = mk_zcontext3
  fun get_base_zcontext _ = L.get (lzcontext3 ())
    |> Lazy_Cat_Util.unlift
  fun get_new_zcontext _ = L.get (parent3 ())
    |> Lazy_Cat_Util.unlift
)
structure Z4 = Extend_Zipper4_Context(
  open Base
  structure Z = Z4
  structure ZO = Zipper4_Optics_Zipper_Data(
    open BaseZO
    type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4
  )
  type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) parent4
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4
  val mk_zcontext = mk_zcontext4
  fun get_base_zcontext _ = L.get (lzcontext4 ())
    |> Lazy_Cat_Util.unlift
  fun get_new_zcontext _ = L.get (parent4 ())
    |> Lazy_Cat_Util.unlift
)

structure Base =
struct
  structure MB = Move_Base(AA.A); open MB
  structure SC = Semi_Category(MB); open SC
  open AA AA.A
end
structure Down1 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  fun move _ =
    (Z1.ZO.get_content >>> (N1.get_content &&& N1.get_next)) &&& Z1.ZO.get_zcontext
    >>> arr (fn ((content, next), zcontext) => (next, (content, zcontext)))
    >>> (AA.app' () *** arr (uncurry ZD.zipper #> K))
    >>> Z2.ZM.Zip.move
    |> Lazy_Cat_Util.unlift
end
structure Down2 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  fun move _ =
    (Z2.ZO.get_content >>> (N2.get_content &&& N2.get_next)) &&& Z2.ZO.get_zcontext
    >>> arr (fn ((content, next), zcontext) => (next, (content, zcontext)))
    >>> (AA.app' () *** arr (uncurry ZD.zipper #> K))
    >>> Z3.ZM.Zip.move
    |> Lazy_Cat_Util.unlift
end
structure Down3 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  fun move _ =
    (Z3.ZO.get_content >>> (N3.get_content &&& N3.get_next)) &&& Z3.ZO.get_zcontext
    >>> arr (fn ((content, next), zcontext) => (next, (content, zcontext)))
    >>> (AA.app' () *** arr (uncurry ZD.zipper #> K))
    >>> Z4.ZM.Zip.move
    |> Lazy_Cat_Util.unlift
end
structure Down4 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  fun move _ =
    (Z4.ZO.get_content >>> (N4.get_content &&& N4.get_next)) &&& Z4.ZO.get_zcontext
    >>> arr (fn ((content, next), zcontext) => (next, (content, zcontext)))
    >>> (AA.app' () *** arr (uncurry ZD.zipper #> K))
    >>> Z1.ZM.Zip.move
    |> Lazy_Cat_Util.unlift
end

structure Up1 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  fun move _ = Z1.ZM.Unzip.move
    >>> second (AA.app' () >>> arr ZD.dest_zipper)
    >>> arr (fn (next, {content, zcontext}) => (pair content (K next), zcontext))
    >>> first N4.node
    >>> Z4.ZO.zipper
    |> Lazy_Cat_Util.unlift
end
structure Up2 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  fun move _ = Z2.ZM.Unzip.move
    >>> second (AA.app' () >>> arr ZD.dest_zipper)
    >>> arr (fn (next, {content, zcontext}) => (pair content (K next), zcontext))
    >>> first N1.node
    >>> Z1.ZO.zipper
    |> Lazy_Cat_Util.unlift
end
structure Up3 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  fun move _ = Z3.ZM.Unzip.move
    >>> second (AA.app' () >>> arr ZD.dest_zipper)
    >>> arr (fn (next, {content, zcontext}) => (pair content (K next), zcontext))
    >>> first N2.node
    >>> Z2.ZO.zipper
    |> Lazy_Cat_Util.unlift
end
structure Up4 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  fun move _ = Z4.ZM.Unzip.move
    >>> second (AA.app' () >>> arr ZD.dest_zipper)
    >>> arr (fn (next, {content, zcontext}) => (pair content (K next), zcontext))
    >>> first N3.node
    >>> Z3.ZO.zipper
    |> Lazy_Cat_Util.unlift
end

end

