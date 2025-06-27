(*  Title:      Zippy/pair_zipper5.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
sig
  structure SZ1 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  structure SZ2 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  sharing type SZ2.Z.zipper = SZ1.Z.zipper
  sharing type SZ2.Z.ZM.container = SZ1.Z.ZM.container
  sharing type SZ2.Z.ZD.content = SZ1.Z.ZD.content
  sharing type SZ2.Z.ZD.zcontext = SZ1.Z.ZD.zcontext
  sharing type SZ2.Z.M.t = SZ1.Z.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container =
    @{AllT_args} SZ1.ZSub.ZM.container * @{AllT_args} SZ2.ZSub.ZM.container
  where type @{AllT_args} ZD.content =
    @{AllT_args} SZ1.ZSub.ZD.content * @{AllT_args} SZ2.ZSub.ZD.content
  where type @{AllT_args} ZD.zcontext =
    @{AllT_args} SZ1.ZSub.ZD.zcontext * @{AllT_args} SZ2.ZSub.ZD.zcontext
  where type @{AllT_args} ZD.zipper =
    @{AllT_args} SZ1.ZSub.zipper * @{AllT_args} SZ2.ZSub.zipper
  sharing type M.t = SZ1.Z.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    sharing type Z2.M.t = Z1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
struct

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Morphs"\<close>(
    structure Z1 = Z1.ZM; structure Z2 = Z2.ZM)
  structure ZD = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Data"\<close>(
    structure Z1 = Z1.ZD; structure Z2 = Z2.ZD))
open Z

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure SZ1 =
struct
  structure Z = Z
  structure ZSub = Z1
  structure Zipper = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.zipper
    type @{AllT_args} data = @{AllT_args} ZSub.zipper
    fun lens _ = L.lens_fst (L.id ()))
  structure Container = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZM.container
    type @{AllT_args} data = @{AllT_args} ZSub.ZM.container
    fun lens _ = L.lens_fst (L.id ()))
  structure Content = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.content
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.content
    fun lens _ = L.lens_fst (L.id ()))
  structure ZCtxt = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.zcontext
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.zcontext
    fun lens _ = L.lens_fst (L.id ()))
end
structure SZ2 =
struct
  structure Z = Z
  structure ZSub = Z2
  structure Zipper = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.zipper
    type @{AllT_args} data = @{AllT_args} ZSub.zipper
    fun lens _ = L.lens_snd (L.id ()))
  structure Container = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZM.container
    type @{AllT_args} data = @{AllT_args} ZSub.ZM.container
    fun lens _ = L.lens_snd (L.id ()))
  structure Content = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.content
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.content
    fun lens _ = L.lens_snd (L.id ()))
  structure ZCtxt = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.zcontext
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.zcontext
    fun lens _ = L.lens_snd (L.id ()))
end

end