(*  Title:      HOCLP/pair_zipper5.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ZIPPER"\<close> =
sig
  structure Z1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  structure Z2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZM.container = @{T_args} Z1.ZM.container * @{T_args} Z2.ZM.container
  where type @{T_args} ZO.content = @{T_args} Z1.ZO.content * @{T_args} Z2.ZO.content
  where type @{T_args} ZO.zcontext = @{T_args} Z1.ZO.zcontext * @{T_args} Z2.ZO.zcontext
  where type @{T_args} ZO.zipper = @{T_args} Z1.zipper * @{T_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper"\<close>(
    structure Z1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    structure Z2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    sharing type Z2.M.t = Z1.M.t
    sharing type Z2.ZO.L.lens = Z1.ZO.L.lens
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ZIPPER"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper" ^ "_Moves"\<close>(
    structure Z1 = Z1.ZM; structure Z2 = Z2.ZM)
  structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper" ^ "_Optics"\<close>(
    structure A = Kleisli_Arrow_Arrow_Apply(Z1.M);
    structure Z1 = Z1.ZO; structure Z2 = Z2.ZO)
)
open Z

end