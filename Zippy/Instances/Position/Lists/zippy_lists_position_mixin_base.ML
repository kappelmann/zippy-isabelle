(*  Title:      Zippy/zippy_lists_position_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_POSITION_MIXIN_BASE =
sig
  include ZIPPY_LISTS_BASE

  structure ZP : ZIPPY_POSITION_MIXIN_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type ZP.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type ZP.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type ZP.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
  sharing type ZP.Z{i}.zipper = Z{i}.zipper\<close>\<close>
  sharing type ZP.M.t = M.t
end

functor Zippy_Lists_Position_Mixin_Base(
    Z : ZIPPY_LISTS_BASE
  ) :
  sig
    include ZIPPY_LISTS_POSITION_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZP.ZPos.Z{i}.ZM.container ->
      @{AllT_args} ZP.ZDepth.Z{i}.ZM.container ->
      @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct
open Z
structure Z = Zippy_Node_Position_Mixin_Base(Z)
open Z
end


