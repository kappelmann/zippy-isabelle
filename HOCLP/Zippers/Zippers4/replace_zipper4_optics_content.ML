(*  Title:      HOCLP/replace_zipper4_optics_content.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper4_Optics_Content(
    structure A : KLEISLI_ARROW
    structure Z : ZIPPER4_OPTICS
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    val ncontent :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z.content, ('p1, 'a1, 'a2, 'a3, 'a4) ncontent) Z.L.C.cat
    val dest_ncontent :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) ncontent, ('p1, 'a1, 'a2, 'a3, 'a4) Z.content) Z.L.C.cat
  ) :
    ZIPPER4_OPTICS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper
  =
struct

open Z
type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent

fun content _ = L.comp (L.lens_get_mk ncontent dest_ncontent) (Z.content ())

local structure SC = Semi_Category(A) open SC A
in
fun zipper x = x |> (first dest_ncontent >>> Z.zipper)
fun get_content x = x |> (L.get (content ()))
fun map_content x = x |> (L.modify (content ()))
end

end
