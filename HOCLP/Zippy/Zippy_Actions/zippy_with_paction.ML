(*  Title:      HOCLP/zippy_with_paction.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_WITH_PACTION =
sig
  include ALTERNATING_ZIPPERS4
  structure PAD : ZIPPY_PACTION_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type PAD.L.lens = L.lens
  structure CD : ZIPPY_COPY_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type CD.L.lens = L.lens

  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction
  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy

  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1, 'a1, 'a2,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data
    ) Z1.zipper
  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1, 'a1, 'a2,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data
    ) Z2.zipper
  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1, 'a1, 'a2,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data
    ) Z3.zipper
  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1, 'a1, 'a2,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data
    ) Z4.zipper

  type ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) action = 'p ->
    ('p1, ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move

  val mk_paction : ('p1, ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper4,
      'p * ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) action) cat ->
    ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction
  val dest_paction : ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction ->
    ('p1, ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper4,
      'p * ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) action) cat
  val mk_copy : ('cud -> ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 ->
      ('p1, ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy
  val dest_copy : ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy ->
    'cud -> ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 ->
    ('p1, ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move
end

functor Zippy_With_PAction(
    structure AZ : ALTERNATING_ZIPPERS4
    structure PAD : ZIPPY_PACTION_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) AZ.cat
    sharing type PAD.L.lens = AZ.L.lens
    structure CD : ZIPPY_COPY_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) AZ.cat
    sharing type CD.L.lens = AZ.L.lens
  ) : ZIPPY_WITH_PACTION =
struct

structure PAD = PAD
structure CD = CD
open AZ

(* paction *)
datatype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) paction = PAction of ('p1,
  ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4,
  'p * ('p -> ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move)) cat
withtype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data) Z1.zipper
and ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper2 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data) Z2.zipper
and ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data) Z3.zipper
and ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'a1, 'a2, 'a3, (('p1, 'p, 'a1, 'a2, 'a3, 'a4) paction, 'a4) PAD.paction_data) Z4.zipper

type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) action = 'p ->
  ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move

fun mk_paction Paction = PAction Paction
fun dest_paction (PAction Paction) = Paction

(* copy *)
datatype ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy = Copy of
  'cud -> ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 ->
  ('p1, ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move
withtype ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'p, 'a1, 'a2, (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data, 'a4) zipper1
and ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper2 =
  ('p1, 'p, 'a1, 'a2, (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data, 'a4) zipper2
and ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper3 =
  ('p1, 'p, 'a1, 'a2, (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data, 'a4) zipper3
and ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'p, 'a1, 'a2, (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data, 'a4) zipper4
and ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) paction =
  ('p1, 'p, 'a1, 'a2, (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data, 'a4) paction
and ('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) action =
  ('p1, 'p, 'a1, 'a2, (('p1, 'cud, 'p, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data, 'a4) action

fun mk_copy copy = Copy copy
fun dest_copy (Copy copy) = copy

end
