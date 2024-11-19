(*  Title:      HOCLP/pair_zipper4.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ZIPPER4 =
sig
  structure Z1 : ZIPPER4
  structure Z2 : ZIPPER4
  sharing type Z2.cat = Z1.cat

  include ZIPPER4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zipper =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
  sharing type cat = Z1.cat
end

functor Pair_Zipper4(
    structure A : LAZY_ARROW_ARROW_APPLY
    structure Z1 : ZIPPER4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.A.cat
    structure Z2 : ZIPPER4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) Z1.cat
    sharing type Z2.ZO.L.lens = Z1.ZO.L.lens
  ) : PAIR_ZIPPER4 =
struct

structure Z1 = Z1
structure Z2 = Z2

structure Z = Zipper4(
  structure ZM = Pair_Zipper4_Moves(structure A = A.A; structure Z1 = Z1.ZM; structure Z2 = Z2.ZM)
  structure ZO = Pair_Zipper4_Optics(structure A = A; structure Z1 = Z1.ZO; structure Z2 = Z2.ZO)
)
open Z

end