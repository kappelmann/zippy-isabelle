(*  Title:      HOCLP/replace_zipper_optics_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Optics_Content"\<close>(
    structure A : KLEISLI_ARROW
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.cat
    type @{T_args} ncontent
    val ncontent : (@{ParaT_args}, @{T_args} Z.content, @{T_args} ncontent) Z.L.C.cat
    val dest_ncontent : (@{ParaT_args}, @{T_args} ncontent, @{T_args} Z.content) Z.L.C.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type @{T_args} content = @{T_args} ncontent
    where type @{T_args} zcontext = @{T_args} Z.zcontext
    where type @{T_args} zipper = @{T_args} Z.zipper
  =
struct

open Z
type @{T_args} content = @{T_args} ncontent

fun content _ = L.comp (L.lens_get_mk ncontent dest_ncontent) (Z.content ())

local structure SC = Semi_Category(A) open SC A
in
fun zipper x = x |> (first dest_ncontent >>> Z.zipper)
fun get_content x = x |> (L.get (content ()))
fun map_content x = x |> (L.modify (content ()))
end

end
