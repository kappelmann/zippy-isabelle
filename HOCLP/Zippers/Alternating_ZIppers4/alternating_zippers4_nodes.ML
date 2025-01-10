(*  Title:      HOCLP/alternating_zippers4_nodes.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_ZIPPERS4_NODES_BASE_ARGS =
sig
  structure Z1 : ZIPPER4
  structure Z2 : ZIPPER4
  sharing type Z2.M.t = Z1.M.t
  sharing type Z2.ZO.L.lens = Z1.ZO.L.lens
  structure Z3 : ZIPPER4
  sharing type Z3.M.t = Z1.M.t
  sharing type Z3.ZO.L.lens = Z1.ZO.L.lens
  structure Z4 : ZIPPER4
  sharing type Z4.M.t = Z1.M.t
  sharing type Z4.ZO.L.lens = Z1.ZO.L.lens

  structure N1 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container) Z2.M.t
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z1.cat
  sharing type N1.node = Z1.ZO.content
  sharing type N1.L.lens = Z1.ZO.L.lens
  structure N2 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container) Z3.M.t
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z2.cat
  sharing type N2.node = Z2.ZO.content
  sharing type N2.L.lens = Z2.ZO.L.lens
  structure N3 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container) Z4.M.t
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z3.cat
  sharing type N3.node = Z3.ZO.content
  sharing type N3.L.lens = Z3.ZO.L.lens
  structure N4 : NODE4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container) Z1.M.t
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z4.cat
  sharing type N4.node = Z4.ZO.content
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
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) A.Z4.M.t
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) A.Z1.M.t
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) A.Z2.M.t
  type ('p1, 'a1, 'a2, 'a3, 'a4) parent4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) A.Z3.M.t

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
  where type ('p1, 'a) M.t = ('p1, 'a) A.Z1.M.t
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z1.ZO.L.lens
end

functor Alternating_Zippers4_Nodes(
    structure A : ALTERNATING_ZIPPERS4_NODES_BASE_ARGS
    structure ZD : ZIPPER_DATA
  ) : ALTERNATING_ZIPPERS4_NODES =
struct

structure A = A
open A
structure M : MOVE_BASE = Z1
open M
structure AA = Kleisli_Arrow_Arrow_Apply(M)
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
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) M.t
  ) lzcontext_parent
and ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2 = ZContext2 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext2,
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) M.t
  ) lzcontext_parent
and ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3 = ZContext3 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext3,
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) M.t
  ) lzcontext_parent
and ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4 = ZContext4 of (
    ('p1, 'a1, 'a2, 'a3, 'a4) lzcontext4,
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) M.t
  ) lzcontext_parent
withtype ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N4.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext4) ZD.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N1.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext1) ZD.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N2.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext2) ZD.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4 =
  (('p1, 'a1, 'a2, 'a3, 'a4) N3.content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext3) ZD.zipper

type ('p1, 'a1, 'a2, 'a3, 'a4) parent1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper1) Z4.M.t
type ('p1, 'a1, 'a2, 'a3, 'a4) parent2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper2) Z1.M.t
type ('p1, 'a1, 'a2, 'a3, 'a4) parent3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper3) Z2.M.t
type ('p1, 'a1, 'a2, 'a3, 'a4) parent4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) pzipper4) Z3.M.t

structure Base =
struct
  structure A = struct open AA AA.A end
  structure L = L
  structure ZD = ZD
end
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
fun mk_zcontext1 x = x |> arr (uncurry lzcontext_parent #> ZContext1)
fun mk_zcontext2 x = x |> arr (uncurry lzcontext_parent #> ZContext2)
fun mk_zcontext3 x = x |> arr (uncurry lzcontext_parent #> ZContext3)
fun mk_zcontext4 x = x |> arr (uncurry lzcontext_parent #> ZContext4)

structure LK = Lens_Kleisli(structure A = struct open AA.A AA end; structure L = L)
fun monad_lens l = LK.lens_monad l

fun zcontext1 _ = L.lens_get_mk
  (arr (fn (ZContext1 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext1
fun lzcontext1 _ = L.lens_fst (zcontext1 ())
fun parent1 _ = L.lens_snd (zcontext1 ())
fun pzipper1 _ = monad_lens (parent1 ())

fun zcontext2 _ = L.lens_get_mk
  (arr (fn (ZContext2 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext2
fun lzcontext2 _ = L.lens_fst (zcontext2 ())
fun parent2 _ = L.lens_snd (zcontext2 ())
fun pzipper2 _ = monad_lens (parent2 ())

fun zcontext3 _ = L.lens_get_mk
  (arr (fn (ZContext3 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext3
fun lzcontext3 _ = L.lens_fst (zcontext3 ())
fun parent3 _ = L.lens_snd (zcontext3 ())
fun pzipper3 _ = monad_lens (parent3 ())

fun zcontext4 _ = L.lens_get_mk
  (arr (fn (ZContext4 {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext4
fun lzcontext4 _ = L.lens_fst (zcontext4 ())
fun parent4 _ = L.lens_snd (zcontext4 ())
fun pzipper4 _ = monad_lens (parent4 ())

end

structure Base = struct structure A = struct open AA AA.A end end
structure BaseZO =
struct
  structure A = struct open AA AA.A end
  structure ZD = ZD
  structure L = Z1.ZO.L
end
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
  fun get_base_zcontext x = x |> L.get (lzcontext1 ())
  fun get_new_zcontext x = x |> L.get (parent1 ())
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
  fun get_base_zcontext x = x |> L.get (lzcontext2 ())
  fun get_new_zcontext x = x |> L.get (parent2 ())
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
  fun get_base_zcontext x = x |> L.get (lzcontext3 ())
  fun get_new_zcontext x = x |> L.get (parent3 ())
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
  fun get_base_zcontext x = x |> L.get (lzcontext4 ())
  fun get_new_zcontext x = x |> L.get (parent4 ())
)

structure Base =
struct
  structure MB = Move_Base(AA.K.M); open MB
  structure SC = Semi_Category(MB); open SC
  structure M = Monad(M); open M
  open AA AA.A
end
structure Down1 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  fun move x = x |>
    ((Z1.ZO.get_content >>> (N1.get_content &&& N1.get_next)) &&& Z1.ZO.get_zcontext
    >>> (fn ((content, next), zcontext) => next
    >>= (fn next => Z2.ZM.Zip.move (next, ZD.zipper content zcontext |> M.pure))))
end
structure Down2 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  fun move x = x |>
    ((Z2.ZO.get_content >>> (N2.get_content &&& N2.get_next)) &&& Z2.ZO.get_zcontext
    >>> (fn ((content, next), zcontext) => next
    >>= (fn next => Z3.ZM.Zip.move (next, ZD.zipper content zcontext |> M.pure))))
end
structure Down3 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  fun move x = x |>
    ((Z3.ZO.get_content >>> (N3.get_content &&& N3.get_next)) &&& Z3.ZO.get_zcontext
    >>> (fn ((content, next), zcontext) => next
    >>= (fn next => Z4.ZM.Zip.move (next, ZD.zipper content zcontext |> M.pure))))
end
structure Down4 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  fun move x = x |>
    ((Z4.ZO.get_content >>> (N4.get_content &&& N4.get_next)) &&& Z4.ZO.get_zcontext
    >>> (fn ((content, next), zcontext) => next
    >>= (fn next => Z1.ZM.Zip.move (next, ZD.zipper content zcontext |> M.pure))))
end

structure Up1 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  fun move x = x |>
    (Z1.ZM.Unzip.move
    >>> (fn (next, parent) => parent
    >>= (arr ZD.dest_zipper
    >>> arr (fn {content, zcontext} => (pair content (M.pure next), zcontext))
    >>> first N4.node
    >>> Z4.ZO.zipper)))
end
structure Up2 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
  fun move x = x |>
    (Z2.ZM.Unzip.move
    >>> (fn (next, parent) => parent
    >>= (arr ZD.dest_zipper
    >>> arr (fn {content, zcontext} => (pair content (M.pure next), zcontext))
    >>> first N1.node
    >>> Z1.ZO.zipper)))
end
structure Up3 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  fun move x = x |>
    (Z3.ZM.Unzip.move
    >>> (fn (next, parent) => parent
    >>= (arr ZD.dest_zipper
    >>> arr (fn {content, zcontext} => (pair content (M.pure next), zcontext))
    >>> first N2.node
    >>> Z2.ZO.zipper)))
end
structure Up4 : MOVE4 =
struct
  open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
  fun move x = x |>
    (Z4.ZM.Unzip.move
    >>> (fn (next, parent) => parent
    >>= (arr ZD.dest_zipper
    >>> arr (fn {content, zcontext} => (pair content (M.pure next), zcontext))
    >>> first N3.node
    >>> Z3.ZO.zipper)))
end

end

