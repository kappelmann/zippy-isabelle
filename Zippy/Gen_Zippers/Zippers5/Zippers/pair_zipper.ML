(*  Title:      Zippy/pair_zipper5.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} Z1.ZM.container * @{AllT_args} Z2.ZM.container
  where type @{AllT_args} ZD.content = @{AllT_args} Z1.ZD.content * @{AllT_args} Z2.ZD.content
  where type @{AllT_args} ZD.zcontext = @{AllT_args} Z1.ZD.zcontext * @{AllT_args} Z2.ZD.zcontext
  where type @{AllT_args} ZD.zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    sharing type Z2.M.t = Z1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Moves"\<close>(
    structure Z1 = Z1.ZM; structure Z2 = Z2.ZM)
  structure ZD = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Data"\<close>(
    structure Z1 = Z1.ZD; structure Z2 = Z2.ZD)
)
open Z

end