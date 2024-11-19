(*  Title:      HOCLP/pair_zipper4_optics.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ZIPPER4_OPTICS =
sig
  structure Z1 : ZIPPER4_OPTICS
  structure Z2 : ZIPPER4_OPTICS
  sharing type Z1.L.C.cat = Z2.L.C.cat

  include ZIPPER4_OPTICS
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.content * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.content
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
end

signature LAZY_ARROW_ARROW_APPLY =
sig
  structure A : LAZY_ARROW
  structure AA : LAZY_ARROW_APPLY
  sharing type AA.T.cat = A.T.cat
end

functor Pair_Zipper4_Optics(
    structure A : LAZY_ARROW_ARROW_APPLY
    structure Z1 : ZIPPER4_OPTICS
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.A.cat
    structure Z2 : ZIPPER4_OPTICS
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.A.cat
    sharing type Z2.L.lens = Z1.L.lens
  ) : PAIR_ZIPPER4_OPTICS =
struct

structure Z1 = Z1
structure Z2 = Z2
structure L = Z1.L

type ('p1, 'a1, 'a2, 'a3, 'a4) content =
  ('p1, 'a1, 'a2, 'a3, 'a4) Z1.content * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.content
type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext =
  ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zcontext
type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
  ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper * ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper

structure LP = Pair_Lens(structure AA = A.AA; structure A = A.A; structure L = L)

fun content _ = LP.lens_pair (Z1.content ()) (Z2.content ())
fun zcontext _ = LP.lens_pair (Z1.zcontext ()) (Z2.zcontext ())
fun get_content _ = L.get (content ())
  |> Lazy_Cat_Util.unlift
fun get_zcontext _ = L.get (zcontext ())
  |> Lazy_Cat_Util.unlift
fun map_content _ = L.modify (content ())
  |> Lazy_Cat_Util.unlift
fun map_zcontext _ = L.modify (zcontext ())
  |> Lazy_Cat_Util.unlift

local structure SC = Semi_Category(A.A) open SC A.A
in
fun zipper _ = arr (fn ((c1, c2), (zctxt1, zctxt2)) => ((c1, zctxt1), (c2, zctxt2)))
  >>> (Z1.zipper *** Z2.zipper)
  |> Lazy_Cat_Util.unlift
end

end
