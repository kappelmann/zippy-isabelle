(*  Title:      HOCLP/zipper_optics_zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS_ZIPPER_DATA"\<close> =
sig
  structure ZD : ZIPPER_DATA
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  (* where type @{T_args} zipper = (@{T_args} content, @{T_args} zcontext) ZD.zipper *)
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data"\<close>(
    structure A : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure ZD : ZIPPER_DATA
    type @{T_args} content
    type @{T_args} zcontext
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS_ZIPPER_DATA"\<close>
    where type @{T_args} content = @{T_args} content
    where type @{T_args} zcontext = @{T_args} zcontext
    where type @{T_args} zipper = (@{T_args} content, @{T_args} zcontext) ZD.zipper
  =
struct

structure L = L
structure ZD = ZD

type @{T_args} content = @{T_args} content
type @{T_args} zcontext = @{T_args} zcontext
type @{T_args} zipper = (@{T_args} content, @{T_args} zcontext) ZD.zipper

open A
fun zipper x = x |> arr (uncurry ZD.zipper)

fun zipper_lens _ = L.lens_get_mk
  (A.arr (ZD.dest_zipper #> (fn {content, zcontext} => (content, zcontext)))) zipper
fun content _ = L.lens_fst (zipper_lens ())
fun zcontext _ = L.lens_snd (zipper_lens ())
fun get_content x = x |> L.get (content ())
fun map_content x = x |> L.modify (content ())
fun get_zcontext x = x |> L.get (zcontext ())
fun map_zcontext x = x |> L.modify (zcontext ())

end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data_SLens"\<close>(
    structure ZD : ZIPPER_DATA
    type @{T_args} content
    type @{T_args} zcontext
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS_ZIPPER_DATA"\<close>
    where type @{T_args} content = @{T_args} content
    where type @{T_args} zcontext = @{T_args} zcontext
    where type @{T_args} zipper = (@{T_args} content, @{T_args} zcontext) ZD.zipper
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat
  =
struct

structure L = SLens
structure ZD = ZD
open ZD

type @{T_args} content = @{T_args} content
type @{T_args} zcontext = @{T_args} zcontext
type @{T_args} zipper = (@{T_args} content, @{T_args} zcontext) ZD.zipper

fun zipper x = uncurry ZD.zipper x
fun map_content x = uncurry ZD.map_content x
fun map_zcontext x = uncurry ZD.map_zcontext x

end
