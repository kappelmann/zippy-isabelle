(*  Title:      Zippy/zippy_positions_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_POSITIONS_MIXIN_BASE =
sig
  include ZIPPY_BASE_BASE
  structure ZGPos : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close>
  sharing type ZGPos.M.t = M.t
  structure ZLPos : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close>
  sharing type ZLPos.M.t = M.t
  structure ZDepth : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close>
  sharing type ZDepth.M.t = M.t

  structure SZGPos : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} ZGPos.Z{i}.ZM.container
  where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} ZGPos.Z{i}.zipper
  where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} ZGPos.Z{i}.ZD.content
  where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} ZGPos.Z{i}.ZD.zcontext\<close>\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZGPos.Z.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type SZGPos.Z.Z{i}.zipper = Z{i}.zipper
  sharing type SZGPos.Z.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type SZGPos.Z.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext\<close>\<close>
  sharing type SZGPos.Z.M.t = M.t

  structure SZLPos : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} ZLPos.Z{i}.ZM.container
  where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} ZLPos.Z{i}.zipper
  where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} ZLPos.Z{i}.ZD.content
  where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} ZLPos.Z{i}.ZD.zcontext\<close>\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZLPos.Z.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type SZLPos.Z.Z{i}.zipper = Z{i}.zipper
  sharing type SZLPos.Z.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type SZLPos.Z.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext\<close>\<close>
  sharing type SZLPos.Z.M.t = M.t

  structure SZDepth : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} ZDepth.Z{i}.ZM.container
  where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} ZDepth.Z{i}.zipper
  where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} ZDepth.Z{i}.ZD.content
  where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} ZDepth.Z{i}.ZD.zcontext\<close>\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZDepth.Z.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type SZDepth.Z.Z{i}.zipper = Z{i}.zipper
  sharing type SZDepth.Z.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type SZDepth.Z.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext\<close>\<close>
  sharing type SZDepth.Z.M.t = M.t
end

functor Zippy_Positions_Mixin_Base(
    structure Z : ZIPPY_BASE_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN_BASE
    where type @{ParaT_args encl = "(" ")"} ME.exn = unit
    sharing type Exn.M.t = Z.M.t
  ) :
  sig
    include ZIPPY_POSITIONS_MIXIN_BASE
    structure SZ : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} Z.Z{i}.ZM.container
    where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} Z.Z{i}.zipper
    where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} Z.Z{i}.ZD.content
    where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} Z.Z{i}.ZD.zcontext\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    sharing type SZ.Z.Z{i}.ZM.container = Z{i}.ZM.container
    sharing type SZ.Z.Z{i}.zipper = Z{i}.zipper
    sharing type SZ.Z.Z{i}.ZD.content = Z{i}.ZD.content
    sharing type SZ.Z.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext\<close>\<close>
    sharing type SZ.Z.M.t = M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZGPos.Z{i}.ZM.container ->
      @{AllT_args} ZLPos.Z{i}.ZM.container -> @{AllT_args} ZDepth.Z{i}.ZM.container ->
      @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct

open Exn
structure ZGPos = \<^eval>\<open>pfx_sfx_nargs "Alternating_Global_Position_Zipper"\<close>(Z)
structure ZLPos = \<^eval>\<open>pfx_sfx_nargs "Alternating_Local_Position_Zipper"\<close>(
  \<^eval>\<open>sfx_T_nargs "Position_Zipper"\<close>(ME))
structure ZDepth = \<^eval>\<open>pfx_sfx_nargs "Alternating_Depth_Zipper"\<close>(Z)

structure PZ1 = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = ZLPos; structure AZ2 = ZDepth)
structure PZ2 = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = ZGPos; structure AZ2 = PZ1)
structure Z = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = Z; structure AZ2 = PZ2)

open Z

structure SZ = Z.SZ1
structure SZGPos = \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
  structure ASZ1 = Z.SZ2; structure ASZ2 = PZ2.SZ1)
structure SZPZ1 = \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
  structure ASZ1 = Z.SZ2; structure ASZ2 = PZ2.SZ2)
structure SZLPos = \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
  structure ASZ1 = SZPZ1; structure ASZ2 = PZ1.SZ1)
structure SZDepth = \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
  structure ASZ1 = SZPZ1; structure ASZ2 = PZ1.SZ2)

fun container gp lp d c = (c, (gp, (lp, d)))
fun init_container c = container ZGPos.init_path ((), ME.throw ()) ZDepth.init_depth c
\<^imap>\<open>\<open>{i}\<close> => \<open>
val container{i} = container
val init_container{i} = init_container
\<close>\<close>

end
