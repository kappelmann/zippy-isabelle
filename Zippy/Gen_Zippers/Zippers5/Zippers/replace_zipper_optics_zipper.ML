(*  Title:      Zippy/replace_zipper_optics_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Optics_Zipper"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.cat
    type @{AllT_args} nzipper
    val nzipper : (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} nzipper) Z.L.C.cat
    val dest_nzipper : (@{ParaT_args} @{AllT_args} nzipper, @{AllT_args} Z.zipper) Z.L.C.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type @{AllT_args} content = @{AllT_args} Z.content
    where type @{AllT_args} zcontext = @{AllT_args} Z.zcontext
    where type @{AllT_args} zipper = @{AllT_args} nzipper
  =
struct

open Z
type @{AllT_args} zipper = @{AllT_args} nzipper

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC A
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
