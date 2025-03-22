(*  Title:      HOCLP/replace_zipper_optics_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Optics_Content"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.cat
    type @{AllT_args} ncontent
    val ncontent : (@{ParaT_args} @{AllT_args} Z.content, @{AllT_args} ncontent) Z.L.C.cat
    val dest_ncontent : (@{ParaT_args} @{AllT_args} ncontent, @{AllT_args} Z.content) Z.L.C.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type @{AllT_args} content = @{AllT_args} ncontent
    where type @{AllT_args} zcontext = @{AllT_args} Z.zcontext
    where type @{AllT_args} zipper = @{AllT_args} Z.zipper
  =
struct

open Z
type @{AllT_args} content = @{AllT_args} ncontent

fun content _ = L.comp (L.lens_get_mk ncontent dest_ncontent) (Z.content ())

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC A
in
fun zipper x = x |> (first dest_ncontent >>> Z.zipper)
fun get_content x = x |> (L.get (content ()))
fun map_content x = x |> (L.modify (content ()))
end

end
