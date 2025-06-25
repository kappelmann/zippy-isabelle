(*  Title:      Zippy/zippy_node_positions_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE_POSITIONS_MIXIN_BASE =
sig
  include ZIPPY_NODE_BASE

  structure ZP : ZIPPY_POSITIONS_MIXIN_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type ZP.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type ZP.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type ZP.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
  sharing type ZP.Z{i}.zipper = Z{i}.zipper\<close>\<close>
  sharing type ZP.M.t = M.t
end

functor Zippy_Node_Positions_Mixin_Base(
    structure Z : ZIPPY_NODE_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN_BASE
    where type @{ParaT_args encl = "(" ")"} ME.exn = unit
    sharing type Exn.M.t = Z.M.t
  ) :
  sig
    include ZIPPY_NODE_POSITIONS_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZP.ZGPos.Z{i}.ZM.container ->
      @{AllT_args} ZP.ZLPos.Z{i}.ZM.container -> @{AllT_args} ZP.ZDepth.Z{i}.ZM.container ->
      @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct
open Z
structure ZP = Zippy_Positions_Mixin_Base(structure Z = Z; structure Exn = Exn)
open ZP
structure SZN = \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
  structure ASZ1 = SZ; structure ASZ2 = Z.SZN)
end
