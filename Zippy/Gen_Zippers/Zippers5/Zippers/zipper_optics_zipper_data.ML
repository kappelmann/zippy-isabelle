(*  Title:      HOCLP/zipper_optics_zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS_ZIPPER_DATA"\<close> =
sig
  structure ZD : \<^eval>\<open>sfx_ParaT_nargs "ZIPPER_DATA"\<close>
  include \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  (* where type @{AllT_args} zipper = (@{AllT_args} content, @{AllT_args} zcontext) ZD.zipper *)
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Optics_Zipper_Data"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) A.cat
    structure ZD : \<^eval>\<open>sfx_ParaT_nargs "ZIPPER_DATA"\<close>
    type @{AllT_args} content
    type @{AllT_args} zcontext
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS_ZIPPER_DATA"\<close>
    where type @{AllT_args} content = @{AllT_args} content
    where type @{AllT_args} zcontext = @{AllT_args} zcontext
    where type @{AllT_args} zipper = (@{AllT_args} content, @{AllT_args} zcontext) ZD.zipper
  =
struct

structure L = L
structure ZD = ZD

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} zcontext = @{AllT_args} zcontext
type @{AllT_args} zipper = (@{AllT_args} content, @{AllT_args} zcontext) ZD.zipper

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

functor \<^eval>\<open>sfx_T_nargs "Zipper_Optics_Zipper_Data_SLens"\<close>(
    structure ZD : \<^eval>\<open>sfx_ParaT_nargs "ZIPPER_DATA"\<close>
    type @{AllT_args} content
    type @{AllT_args} zcontext
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS_ZIPPER_DATA"\<close>
    where type @{AllT_args} content = @{AllT_args} content
    where type @{AllT_args} zcontext = @{AllT_args} zcontext
    where type @{AllT_args} zipper = (@{AllT_args} content, @{AllT_args} zcontext) ZD.zipper
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b)
      \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close>
  =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure ZD = ZD
open ZD

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} zcontext = @{AllT_args} zcontext
type @{AllT_args} zipper = (@{AllT_args} content, @{AllT_args} zcontext) ZD.zipper

fun zipper x = uncurry ZD.zipper x
fun map_content x = uncurry ZD.map_content x
fun map_zcontext x = uncurry ZD.map_zcontext x

end
