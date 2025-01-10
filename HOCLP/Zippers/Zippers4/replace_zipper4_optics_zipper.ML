(*  Title:      HOCLP/replace_zipper4_optics_zipper.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Zipper4_Optics_Zipper(
    structure A : KLEISLI_ARROW
    structure Z : ZIPPER4_OPTICS
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
    val nzipper :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper) Z.L.C.cat
    val dest_nzipper :
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nzipper, ('p1, 'a1, 'a2, 'a3, 'a4) Z.zipper) Z.L.C.cat
  ) :
    ZIPPER4_OPTICS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper
  =
struct

open Z
type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) nzipper

local structure SC = Semi_Category(A) open SC A
in
fun zipper x = x |> (Z.zipper >>> nzipper)
fun get_content x = x |> (dest_nzipper >>> Z.get_content)
fun get_zcontext x = x |> (dest_nzipper >>> Z.get_zcontext)

fun map_content x = x |> (second dest_nzipper >>> Z.map_content >>> nzipper)
fun map_zcontext x = x |> (second dest_nzipper >>> Z.map_zcontext >>> nzipper)

fun content _ = L.lens get_content map_content
fun zcontext _ = L.lens get_zcontext map_zcontext
end

end
