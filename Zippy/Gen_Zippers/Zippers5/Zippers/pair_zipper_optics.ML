(*  Title:      HOCLP/pair_zipper_optics.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_OPTICS"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  sharing type Z2.L.C.cat = Z1.L.C.cat

  include \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  where type @{AllT_args} content = @{AllT_args} Z1.content * @{AllT_args} Z2.content
  where type @{AllT_args} zcontext = @{AllT_args} Z1.zcontext * @{AllT_args} Z2.zcontext
  where type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Optics"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ARROW_APPLY"\<close>
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.A.cat
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.A.cat
    sharing type Z2.L.lens = Z1.L.lens
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_OPTICS"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2
structure L = Z1.L

type @{AllT_args} content = @{AllT_args} Z1.content * @{AllT_args} Z2.content
type @{AllT_args} zcontext = @{AllT_args} Z1.zcontext * @{AllT_args} Z2.zcontext
type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper

structure LP = \<^eval>\<open>sfx_ParaT_nargs "Pair_Lens"\<close>(
  structure AA = A.AA; structure A = A.A; structure L = L)

fun content _ = LP.lens_pair (Z1.content ()) (Z2.content ())
fun zcontext _ = LP.lens_pair (Z1.zcontext ()) (Z2.zcontext ())
fun get_content x = x |> L.get (content ())
fun get_zcontext x = x |>L.get (zcontext ())
fun map_content x = x |>L.modify (content ())
fun map_zcontext x = x |>L.modify (zcontext ())

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A.A) open SC A.A
in
fun zipper x = x |> (arr (fn ((c1, c2), (zctxt1, zctxt2)) => ((c1, zctxt1), (c2, zctxt2)))
  >>> (Z1.zipper *** Z2.zipper))
end

end
