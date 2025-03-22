(*  Title:      HOCLP/pair_zipper5.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} Z1.ZM.container * @{AllT_args} Z2.ZM.container
  where type @{AllT_args} ZO.content = @{AllT_args} Z1.ZO.content * @{AllT_args} Z2.ZO.content
  where type @{AllT_args} ZO.zcontext = @{AllT_args} Z1.ZO.zcontext * @{AllT_args} Z2.ZO.zcontext
  where type @{AllT_args} ZO.zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    sharing type Z2.M.t = Z1.M.t
    sharing type Z2.ZO.L.lens = Z1.ZO.L.lens
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Moves"\<close>(
    structure Z1 = Z1.ZM; structure Z2 = Z2.ZM)
  structure ZO = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Optics"\<close>(
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(Z1.M);
    structure Z1 = Z1.ZO; structure Z2 = Z2.ZO)
)
open Z

end