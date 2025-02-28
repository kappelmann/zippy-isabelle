(*  Title:      HOCLP/replace_zipper_optics_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Optics_Zipper"\<close>(
    structure A : KLEISLI_ARROW
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.cat
    type @{T_args} nzipper
    val nzipper : (@{ParaT_args}, @{T_args} Z.zipper, @{T_args} nzipper) Z.L.C.cat
    val dest_nzipper : (@{ParaT_args}, @{T_args} nzipper, @{T_args} Z.zipper) Z.L.C.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type @{T_args} content = @{T_args} Z.content
    where type @{T_args} zcontext = @{T_args} Z.zcontext
    where type @{T_args} zipper = @{T_args} nzipper
  =
struct

open Z
type @{T_args} zipper = @{T_args} nzipper

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
