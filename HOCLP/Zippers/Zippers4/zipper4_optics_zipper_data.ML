(*  Title:      HOCLP/zipper4_optics_zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER4_OPTICS_ZIPPER_DATA =
sig
  structure ZD : ZIPPER_DATA
  include ZIPPER4_OPTICS
  (* where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
    (('p1, 'a1, 'a2, 'a3, 'a4) content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) ZD.zipper *)
end

functor Zipper4_Optics_Zipper_Data(
    structure A : LAZY_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure ZD : ZIPPER_DATA
    type ('p1, 'a1, 'a2, 'a3, 'a4) content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
  ) :
    ZIPPER4_OPTICS_ZIPPER_DATA
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
      (('p1, 'a1, 'a2, 'a3, 'a4) content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) ZD.zipper
  =
struct

structure L = L
structure ZD = ZD

type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
  (('p1, 'a1, 'a2, 'a3, 'a4) content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) ZD.zipper

open A
fun zipper _ = arr (uncurry ZD.zipper)
  |> Lazy_Cat_Util.unlift

fun zipper_lens _ = L.lens_get_mk
  (A.arr (ZD.dest_zipper #> (fn {content, zcontext} => (content, zcontext)))) zipper
fun content _ = L.lens_fst (zipper_lens ())
fun zcontext _ = L.lens_snd (zipper_lens ())
fun get_content _ = L.get (content ())
  |> Lazy_Cat_Util.unlift
fun map_content _ = L.modify (content ())
  |> Lazy_Cat_Util.unlift
fun get_zcontext _ = L.get (zcontext ())
  |> Lazy_Cat_Util.unlift
fun map_zcontext _ = L.modify (zcontext ())
  |> Lazy_Cat_Util.unlift

end

functor Zipper4_Optics_Zipper_Data_SLens(
    structure ZD : ZIPPER_DATA
    type ('p1, 'a1, 'a2, 'a3, 'a4) content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
  ) :
    ZIPPER4_OPTICS_ZIPPER_DATA
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
      (('p1, 'a1, 'a2, 'a3, 'a4) content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) ZD.zipper
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat
  =
struct

structure L = SLens
structure ZD = ZD
open ZD

type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
type ('p1, 'a1, 'a2, 'a3, 'a4) zipper =
  (('p1, 'a1, 'a2, 'a3, 'a4) content, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) ZD.zipper

fun zipper x = uncurry ZD.zipper x
fun map_content x = uncurry ZD.map_content x
fun map_zcontext x = uncurry ZD.map_zcontext x

end
