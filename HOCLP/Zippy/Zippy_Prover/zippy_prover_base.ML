(*  Title:      HOCLP/zippy_prover_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_BASE =
sig
  include ALTERNATING_ZIPPERS4

  structure PAD : ZIPPY_PACTION_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type PAD.L.lens = L.lens
  structure CD : ZIPPY_COPY_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type CD.L.lens = L.lens

  structure RD : ZIPPY_RESULT_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type RD.L.lens = L.lens

  structure GCSD : ZIPPY_GOAL_CLUSTERS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type GCSD.L.lens = L.lens
  structure GCD : ZIPPY_GOAL_CLUSTER_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type GCD.L.lens = L.lens
  structure FD : ZIPPY_FOCUS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type FD.L.lens = L.lens

  structure GCS : ZIPPY_GOAL_CLUSTERS
  structure GC : ZIPPY_GOAL_CLUSTER
  sharing type GC.GCS.gclusters = GCS.gclusters
  sharing type GC.GCS.gcpos = GCS.gcpos
  structure F : ZIPPY_FOCUS
  sharing type F.GCS.gclusters = GCS.gclusters
  sharing type F.GCS.gcpos = GCS.gcpos

  structure AND : ZIPPY_ACTION_NUM_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type AND.L.lens = L.lens

  structure CO : COROUTINE
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) cat

  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults

  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1,
      (GCS.gclusters, 'a1) GCSD.gclusters_data,
      (GC.gcluster, 'a2) GCD.gcluster_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction,
        (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
          (F.focus,
            (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data) PAD.paction_data
    ) Z1.zipper
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1,
      (GCS.gclusters, 'a1) GCSD.gclusters_data,
      (GC.gcluster, 'a2) GCD.gcluster_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction,
        (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
          (F.focus,
            (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data) PAD.paction_data
    ) Z2.zipper
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1,
      (GCS.gclusters, 'a1) GCSD.gclusters_data,
      (GC.gcluster, 'a2) GCD.gcluster_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction,
        (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
          (F.focus,
            (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data) PAD.paction_data
    ) Z3.zipper
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1,
      (GCS.gclusters, 'a1) GCSD.gclusters_data,
      (GC.gcluster, 'a2) GCD.gcluster_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy, 'a3) CD.copy_data,
      (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction,
        (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
        (F.focus,
          (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data) PAD.paction_data
    ) Z4.zipper

  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) action = 'p ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move

  val mk_paction : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4,
      'p * ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) action) cat ->
    ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction
  val dest_paction : ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4,
      'p * ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) action) cat

  val mk_copy : ('cud -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
      ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy
  val dest_copy : ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy ->
    'cud -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move

  val mk_presults : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4, 'p, 'r) CO.acoroutine ->
    ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults
  val dest_presults : ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4, 'p, 'r) CO.acoroutine

end

functor Zippy_Prover_Base(
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure GC : ZIPPY_GOAL_CLUSTER
    sharing type GC.GCS.gcpos = GCS.gcpos
    sharing type GC.GCS.gclusters = GCS.gclusters
    structure F : ZIPPY_FOCUS
    sharing type F.GCS.gcpos = GCS.gcpos
    sharing type F.GCS.gclusters = GCS.gclusters
    structure Z : ZIPPY_WITH_GOALS
    structure AND : ZIPPY_ACTION_NUM_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.Z.cat
    sharing type AND.L.lens = Z.Z.Z.L.lens
    structure CO : COROUTINE
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) Z.Z.Z.cat
  ) : ZIPPY_PROVER_BASE =
struct

open Z.Z.Z
local open Z.Z in
structure RD = RD
end
local open Z in
structure GCSD = GCSD
structure GCD = GCD
structure FD = FD
end

structure GCS = GCS
structure GC = GC
structure F = F
structure AND = AND
structure CO = CO

type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1, GCS.gclusters, GC.gcluster,
  'cud, 'p, 'r, F.focus, 'a1, 'a2, 'a3, 'a4) Z.zipper1
and ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1, GCS.gclusters, GC.gcluster,
  'cud, 'p, 'r, F.focus, 'a1, 'a2, 'a3, 'a4) Z.zipper2
and ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1, GCS.gclusters, GC.gcluster,
  'cud, 'p, 'r, F.focus, 'a1, 'a2, 'a3, 'a4) Z.zipper3
and ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1, GCS.gclusters, GC.gcluster,
  'cud, 'p, 'r, F.focus, 'a1, 'a2, 'a3, 'a4) Z.zipper4

(* presults *)
datatype ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults = PResults of
  ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4, 'p, 'r) CO.acoroutine
withtype ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1, 'cud, 'p,
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults, 'a1, 'a2, 'a3, (int, 'a4) AND.action_num_data)
  zipper1
and ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1, 'cud, 'p,
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults, 'a1, 'a2, 'a3, (int, 'a4) AND.action_num_data)
  zipper2
and ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1, 'cud, 'p,
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults, 'a1, 'a2, 'a3, (int, 'a4) AND.action_num_data)
  zipper3
and ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1, 'cud, 'p,
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults, 'a1, 'a2, 'a3, (int, 'a4) AND.action_num_data)
  zipper4

fun mk_presults pr = PResults pr
fun dest_presults (PResults pr) = pr

(*necessary evil: add all missing instantiations to the base type definitions*)
type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction = ('p1, 'cud, 'p,
    (GCS.gclusters, 'a1) GCSD.gclusters_data,
    (GC.gcluster, 'a2) GCD.gcluster_data,
    'a3,
    (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
      (F.focus,
        (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data
  ) Z.Z.Z.paction
type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy = ('p1, 'cud, 'p,
    (GCS.gclusters, 'a1) GCSD.gclusters_data,
    (GC.gcluster, 'a2) GCD.gcluster_data,
    'a3,
    (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
      (F.focus,
        (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data
  ) Z.Z.Z.copy
type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) action = ('p1, 'cud, 'p,
    (GCS.gclusters, 'a1) GCSD.gclusters_data,
    (GC.gcluster, 'a2) GCD.gcluster_data,
    'a3,
    (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults,
      (F.focus,
        (int, 'a4) AND.action_num_data) FD.focus_data) RD.result_data
  ) Z.Z.Z.action
(*end of necessary evil*)
end
