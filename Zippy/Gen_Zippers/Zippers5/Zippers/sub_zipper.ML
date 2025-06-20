(*  Title:      Zippy/sub_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close> =
sig
  structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  structure ZSub : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type ZSub.M.t = Z.M.t

  structure Zipper : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Zipper.container = Z.zipper
  sharing type Zipper.data = ZSub.zipper

  structure Container : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZSub.ZM.container
  sharing type Container.container = Z.ZM.container

  structure Content : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Content.container = Z.ZD.content
  sharing type Content.data = ZSub.ZD.content

  structure ZCtxt : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type ZCtxt.container = Z.ZD.zcontext
  sharing type ZCtxt.data = ZSub.ZD.zcontext
end

functor \<^eval>\<open>sfx_T_nargs "Sub_Zipper_Trans"\<close>(
    structure SZ1 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    structure SZ2 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    sharing type SZ2.Z.zipper = SZ1.ZSub.zipper
    sharing type SZ2.Z.ZM.container = SZ1.ZSub.ZM.container
    sharing type SZ2.Z.ZD.content = SZ1.ZSub.ZD.content
    sharing type SZ2.Z.ZD.zcontext = SZ1.ZSub.ZD.zcontext
    sharing type SZ2.Z.M.t = SZ1.Z.M.t
  ) :
    \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    where type @{AllT_args} Z.zipper = @{AllT_args} SZ1.Z.zipper
    where type @{AllT_args} Z.ZM.container = @{AllT_args} SZ1.Z.ZM.container
    where type @{AllT_args} Z.ZD.content = @{AllT_args} SZ1.Z.ZD.content
    where type @{AllT_args} Z.ZD.zcontext = @{AllT_args} SZ1.Z.ZD.zcontext
    where type @{AllT_args} ZSub.zipper = @{AllT_args} SZ2.ZSub.zipper
    where type @{AllT_args} ZSub.ZM.container = @{AllT_args} SZ2.ZSub.ZM.container
    where type @{AllT_args} ZSub.ZD.content = @{AllT_args} SZ2.ZSub.ZD.content
    where type @{AllT_args} ZSub.ZD.zcontext = @{AllT_args} SZ2.ZSub.ZD.zcontext
    where type (@{ParaT_args} 'a) Z.M.t = (@{ParaT_args} 'a) SZ1.Z.M.t
=
struct

structure Z = SZ1.Z
structure ZSub = SZ2.ZSub

structure Zipper = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.Zipper
  structure L2 = SZ2.Zipper)
structure Container = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.Container
  structure L2 = SZ2.Container)
structure Content = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.Content
  structure L2 = SZ2.Content)
structure ZCtxt = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.ZCtxt
  structure L2 = SZ2.ZCtxt)

end

