(*  Title:      Zippy/sub_alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close> =
sig
  structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  structure ZSub : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  sharing type ZSub.M.t = Z.M.t

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  sharing type SZ{i}.Z.zipper = Z.Z{i}.zipper
  sharing type SZ{i}.Z.ZM.container = Z.Z{i}.ZM.container
  sharing type SZ{i}.Z.ZD.content = Z.Z{i}.ZD.content
  sharing type SZ{i}.Z.ZD.zcontext = Z.Z{i}.ZD.zcontext
  sharing type SZ{i}.ZSub.zipper = ZSub.Z{i}.zipper
  sharing type SZ{i}.ZSub.ZM.container = ZSub.Z{i}.ZM.container
  sharing type SZ{i}.ZSub.ZD.content = ZSub.Z{i}.ZD.content
  sharing type SZ{i}.ZSub.ZD.zcontext = ZSub.Z{i}.ZD.zcontext
  sharing type SZ{i}.Z.M.t = Z.M.t\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
    structure ASZ1 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    structure ASZ2 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    sharing type ASZ2.Z.Z{i}.zipper = ASZ1.ZSub.Z{i}.zipper
    sharing type ASZ2.Z.Z{i}.ZM.container = ASZ1.ZSub.Z{i}.ZM.container
    sharing type ASZ2.Z.Z{i}.ZD.content = ASZ1.ZSub.Z{i}.ZD.content
    sharing type ASZ2.Z.Z{i}.ZD.zcontext = ASZ1.ZSub.Z{i}.ZD.zcontext\<close>\<close>
    sharing type ASZ1.Z.M.t = ASZ2.Z.M.t
  ) :
    \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z.Z{i}.zipper = @{AllT_args} ASZ1.Z.Z{i}.zipper
    where type @{AllT_args} Z.Z{i}.ZM.container = @{AllT_args} ASZ1.Z.Z{i}.ZM.container
    where type @{AllT_args} Z.Z{i}.ZD.content = @{AllT_args} ASZ1.Z.Z{i}.ZD.content
    where type @{AllT_args} Z.Z{i}.ZD.zcontext = @{AllT_args} ASZ1.Z.Z{i}.ZD.zcontext
    where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} ASZ2.ZSub.Z{i}.zipper
    where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} ASZ2.ZSub.Z{i}.ZM.container
    where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} ASZ2.ZSub.Z{i}.ZD.content
    where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} ASZ2.ZSub.Z{i}.ZD.zcontext\<close>\<close>
    where type (@{ParaT_args} 'a) Z.M.t = (@{ParaT_args} 'a) ASZ1.Z.M.t
=
struct

structure Z = ASZ1.Z
structure ZSub = ASZ2.ZSub

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure SZ{i} = \<^eval>\<open>sfx_T_nargs "Sub_Zipper_Trans"\<close>(
  structure SZ1 = ASZ1.SZ{i}
  structure SZ2 = ASZ2.SZ{i})\<close>\<close>

end