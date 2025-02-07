(*  Title:      HOCLP/zippy_with_paction.ML
    Author:     Kevin Kappelmann

Zippy with prioritised actions.
*)
signature ZIPPY_WITH_PACTION =
sig
  type copy_update_data
  type prio

  structure CD : KLEISLI_ZIPPY_COPY_DATA
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more
  structure PAD : ZIPPY_PACTION_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
  sharing type PAD.L.lens = CD.L.lens
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more
  structure PD : ZIPPY_PRIO_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
  sharing type PD.L.lens = CD.L.lens
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more

  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy

  include ALTERNATING_ZIPPERS5_NODES
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N3.content =
    (('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more) CD.copy_data
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N4.content =
    (('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more) PAD.paction_data
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N5.content =
    (prio, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more) PD.prio_data
  where type ('p1, 'a) M.t = ('p1, 'a) CD.K.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) CD.L.lens

  val mk_copy : (copy_update_data -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z3.zipper ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z1.zipper) hom_move) ->
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy
  val dest_copy : ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy -> copy_update_data ->
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z3.zipper ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z1.zipper) hom_move

  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action = prio ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper) hom_move

  val mk_paction : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper,
    prio * ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action) cat -> ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction
  val dest_paction : ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, prio * ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action) cat
end

functor Zippy_With_PAction(
    type copy_update_data
    type prio
    structure CD : KLEISLI_ZIPPY_COPY_DATA
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more
    structure PAD : ZIPPY_PACTION_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
    sharing type PAD.L.lens = CD.L.lens
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more
    structure PD : ZIPPY_PRIO_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) CD.L.C.cat
    sharing type PD.L.lens = CD.L.lens
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more

    structure Z : ALTERNATING_ZIPPERS5_NODES
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N3.content = 'a3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N4.content = 'a4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) N5.content = 'a5
    where type ('p1, 'a) M.t = ('p1, 'a) CD.K.M.t
    where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) PAD.L.lens
  ) : ZIPPY_WITH_PACTION =
struct

type copy_update_data = copy_update_data
type prio = prio
structure CD = CD
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more
structure PAD = PAD
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more
structure PD = PD
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more

open Z

(* paction *)
datatype ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) paction = PAction of
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) zipper4, prio *
    (prio -> ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) zipper4) hom_move)) cat
withtype ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) zipper1 = ('p1, 'a1, 'a2, 'a3,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) paction, 'padm) PAD.paction_data, 'a5) Z1.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) zipper3 = ('p1, 'a1, 'a2, 'a3,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) paction, 'padm) PAD.paction_data, 'a5) Z3.zipper
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) zipper4 = ('p1, 'a1, 'a2, 'a3,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm) paction, 'padm) PAD.paction_data, 'a5) Z4.zipper

fun mk_paction paction = PAction paction
fun dest_paction (PAction paction) = paction

(* copy *)
datatype ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) copy = Copy of copy_update_data ->
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) zipper3 ->
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) zipper1) hom_move
withtype ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) zipper1 = ('p1, 'a1, 'a2,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) copy, 'cdm) CD.copy_data, 'a4, 'a5, 'padm) zipper1
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) zipper3 = ('p1, 'a1, 'a2,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) copy, 'cdm) CD.copy_data, 'a4, 'a5, 'padm) zipper3
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) zipper4 = ('p1, 'a1, 'a2,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) copy, 'cdm) CD.copy_data, 'a4, 'a5, 'padm) zipper4
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) paction = ('p1, 'a1, 'a2,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm) copy, 'cdm) CD.copy_data, 'a4, 'a5, 'padm) paction

fun mk_copy copy = Copy copy
fun dest_copy (Copy copy) = copy

type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm, 'pdm) zipper1 =
  ('p1, 'a1, 'a2, 'a3, 'a4, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) zipper1
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm, 'pdm) zipper3 =
  ('p1, 'a1, 'a2, 'a3, 'a4, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) zipper3
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm, 'pdm) zipper4 =
  ('p1, 'a1, 'a2, 'a3, 'a4, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) zipper4
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm, 'pdm) paction =
  ('p1, 'a1, 'a2, 'a3, 'a4, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) paction
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'padm, 'cdm, 'pdm) copy =
  ('p1, 'a1, 'a2, 'a3, 'a4, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) copy

type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zipper4 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more) zipper4
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more) paction
and ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more,
  ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more) copy

type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action = prio ->
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zipper4) hom_move

structure Z = Instantiate_Alternating_Zippers5_Nodes(
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1 = 'a1
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2 = 'a2
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3 =
    (('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more) CD.copy_data
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4 =
    (('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more) PAD.paction_data
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5 =
    (prio, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more) PD.prio_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_PAction(
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5
    structure Z : ZIPPY_WITH_PACTION
  ) :
    ZIPPY_WITH_PACTION
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.N1.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.N1.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.N2.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.N2.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext5 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext5
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper5 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper5
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.cd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pad_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.paction
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.copy =
struct
open Z
structure Base =
struct
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5
end
structure Z = Instantiate_Alternating_Zippers5_Nodes(open Base; structure Z = Z)
open Z
end
