(*  Title:      HOCLP/zippy_with_result.ML
    Author:     Kevin Kappelmann

Action result(s).
*)
signature ZIPPY_WITH_RESULT =
sig
  structure Z : ZIPPY_WITH_PACTION
  structure RD : ZIPPY_RESULT_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.cat
  sharing type RD.L.lens = Z.L.lens

  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
    ('r, 'a4) RD.result_data) Z.zipper1
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
    ('r, 'a4) RD.result_data) Z.zipper2
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
    ('r, 'a4) RD.result_data) Z.zipper3
  type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
    ('r, 'a4) RD.result_data) Z.zipper4
end

functor Zippy_With_Result(
    structure Z : ZIPPY_WITH_PACTION
    structure RD : ZIPPY_RESULT_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.cat
    sharing type RD.L.lens = Z.L.lens
  ) : ZIPPY_WITH_RESULT =
struct

structure Z = Z
structure RD = RD

type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
  ('r, 'a4) RD.result_data) Z.zipper1
type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
  ('r, 'a4) RD.result_data) Z.zipper2
type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
  ('r, 'a4) RD.result_data) Z.zipper3
type ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 = ('p1, 'cud, 'p, 'a1, 'a2, 'a3,
  ('r, 'a4) RD.result_data) Z.zipper4

end
