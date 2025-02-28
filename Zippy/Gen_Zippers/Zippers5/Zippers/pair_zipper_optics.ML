(*  Title:      HOCLP/pair_zipper_optics.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ZIPPER" ^ "_OPTICS"\<close> =
sig
  structure Z1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  structure Z2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  sharing type Z2.L.C.cat = Z1.L.C.cat

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  where type @{T_args} content = @{T_args} Z1.content * @{T_args} Z2.content
  where type @{T_args} zcontext = @{T_args} Z1.zcontext * @{T_args} Z2.zcontext
  where type @{T_args} zipper = @{T_args} Z1.zipper * @{T_args} Z2.zipper
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper" ^ "_Optics"\<close>(
    structure A : KLEISLI_ARROW_ARROW_APPLY
    structure Z1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.A.cat
    structure Z2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.A.cat
    sharing type Z2.L.lens = Z1.L.lens
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ZIPPER" ^ "_OPTICS"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2
structure L = Z1.L

type @{T_args} content = @{T_args} Z1.content * @{T_args} Z2.content
type @{T_args} zcontext = @{T_args} Z1.zcontext * @{T_args} Z2.zcontext
type @{T_args} zipper = @{T_args} Z1.zipper * @{T_args} Z2.zipper

structure LP = Pair_Lens(structure AA = A.AA; structure A = A.A; structure L = L)

fun content _ = LP.lens_pair (Z1.content ()) (Z2.content ())
fun zcontext _ = LP.lens_pair (Z1.zcontext ()) (Z2.zcontext ())
fun get_content x = x |> L.get (content ())
fun get_zcontext x = x |>L.get (zcontext ())
fun map_content x = x |>L.modify (content ())
fun map_zcontext x = x |>L.modify (zcontext ())

local structure SC = Semi_Category(A.A) open SC A.A
in
fun zipper x = x |> (arr (fn ((c1, c2), (zctxt1, zctxt2)) => ((c1, zctxt1), (c2, zctxt2)))
  >>> (Z1.zipper *** Z2.zipper))
end

end
