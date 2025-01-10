(*  Title:      HOCLP/zippy.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_WITH_GOALS =
sig
  structure Z : ZIPPY_WITH_RESULT
  structure GCSD : ZIPPY_GOAL_CLUSTERS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.cat
  sharing type GCSD.L.lens = Z.Z.L.lens
  structure GCD : ZIPPY_GOAL_CLUSTER_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.cat
  sharing type GCD.L.lens = Z.Z.L.lens
  structure FD : ZIPPY_FOCUS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.cat
  sharing type FD.L.lens = Z.Z.L.lens

  type ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1, 'cud, 'p, 'r,
    ('gcs, 'a1) GCSD.gclusters_data, ('gc, 'a2) GCD.gcluster_data, 'a3, ('f, 'a4) FD.focus_data)
    Z.zipper1
  type ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1, 'cud, 'p, 'r,
    ('gcs, 'a1) GCSD.gclusters_data, ('gc, 'a2) GCD.gcluster_data, 'a3, ('f, 'a4) FD.focus_data)
    Z.zipper2
  type ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1, 'cud, 'p, 'r,
    ('gcs, 'a1) GCSD.gclusters_data, ('gc, 'a2) GCD.gcluster_data, 'a3, ('f, 'a4) FD.focus_data)
    Z.zipper3
  type ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1, 'cud, 'p, 'r,
    ('gcs, 'a1) GCSD.gclusters_data, ('gc, 'a2) GCD.gcluster_data, 'a3, ('f, 'a4) FD.focus_data)
    Z.zipper4
end

functor Zippy_With_Goals(
    structure Z : ZIPPY_WITH_RESULT
    structure GCSD : ZIPPY_GOAL_CLUSTERS_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.cat
    sharing type GCSD.L.lens = Z.Z.L.lens
    structure GCD : ZIPPY_GOAL_CLUSTER_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.cat
    sharing type GCD.L.lens = Z.Z.L.lens
    structure FD : ZIPPY_FOCUS_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z.cat
    sharing type FD.L.lens = Z.Z.L.lens
  ) : ZIPPY_WITH_GOALS =
struct

structure GCSD = GCSD
structure GCD = GCD
structure FD = FD
structure Z = Z

(* action focus *)
type ('p1, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, ('f, 'a4) FD.focus_data) Z.zipper1
and ('p1, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper2 =
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, ('f, 'a4) FD.focus_data) Z.zipper2
and ('p1, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper3 =
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, ('f, 'a4) FD.focus_data) Z.zipper3
and ('p1, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, ('f, 'a4) FD.focus_data) Z.zipper4

(* goal cluster *)
type ('p1, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'cud, 'p, 'r, 'f, 'a1, ('gc, 'a2) GCD.gcluster_data, 'a3, 'a4) zipper1
and ('p1, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper2 =
  ('p1, 'cud, 'p, 'r, 'f, 'a1, ('gc, 'a2) GCD.gcluster_data, 'a3, 'a4) zipper2
and ('p1, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper3 =
  ('p1, 'cud, 'p, 'r, 'f, 'a1, ('gc, 'a2) GCD.gcluster_data, 'a3, 'a4) zipper3
and ('p1, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'cud, 'p, 'r, 'f, 'a1, ('gc, 'a2) GCD.gcluster_data, 'a3, 'a4) zipper4

(* goal clusters *)
type ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper1 =
  ('p1, 'gc, 'cud, 'p, 'r, 'f, ('gcs, 'a1) GCSD.gclusters_data, 'a2, 'a3, 'a4) zipper1
and ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper2 =
  ('p1, 'gc, 'cud, 'p, 'r, 'f, ('gcs, 'a1) GCSD.gclusters_data, 'a2, 'a3, 'a4) zipper2
and ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper3 =
  ('p1, 'gc, 'cud, 'p, 'r, 'f, ('gcs, 'a1) GCSD.gclusters_data, 'a2, 'a3, 'a4) zipper3
and ('p1, 'gcs, 'gc, 'cud, 'p, 'r, 'f, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'gc, 'cud, 'p, 'r, 'f, ('gcs, 'a1) GCSD.gclusters_data, 'a2, 'a3, 'a4) zipper4

end
