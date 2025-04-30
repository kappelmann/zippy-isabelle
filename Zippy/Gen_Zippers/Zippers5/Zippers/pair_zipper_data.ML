(*  Title:      Zippy/pair_zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_DATA"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  sharing type Z2.L.lens = Z1.L.lens
  sharing type Z2.L.K.M.t = Z1.L.K.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  where type @{AllT_args} content = @{AllT_args} Z1.content * @{AllT_args} Z2.content
  where type @{AllT_args} zcontext = @{AllT_args} Z1.zcontext * @{AllT_args} Z2.zcontext
  where type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
  sharing type L.lens = Z1.L.lens
  sharing type L.K.M.t = Z1.L.K.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Data"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type Z2.L.lens = Z1.L.lens
    sharing type Z2.L.K.M.t = Z1.L.K.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_DATA"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2
structure L = Z1.L

type @{AllT_args} content = @{AllT_args} Z1.content * @{AllT_args} Z2.content
type @{AllT_args} zcontext = @{AllT_args} Z1.zcontext * @{AllT_args} Z2.zcontext
type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper

structure CO = \<^eval>\<open>sfx_T_nargs "Pair_Structured_Lens"\<close>(
  structure L1 = Z1.CO; structure L2 = Z2.CO)
structure ZCTXT = \<^eval>\<open>sfx_T_nargs "Pair_Structured_Lens"\<close>(
  structure L1 = Z1.ZCTXT; structure L2 = Z2.ZCTXT)

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(L.C)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(L.K.M)
  open SC A
in
fun zipper x = x |> (arr (fn ((c1, c2), (zctxt1, zctxt2)) => ((c1, zctxt1), (c2, zctxt2)))
  >>> (Z1.zipper *** Z2.zipper))
end

end
