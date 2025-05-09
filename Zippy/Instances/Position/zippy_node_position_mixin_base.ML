(*  Title:      Zippy/zippy_node_position_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE_POSITION_MIXIN_BASE =
sig
  include ZIPPY_NODE_BASE

  structure ZP : ZIPPY_POSITION_MIXIN_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type ZP.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type ZP.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type ZP.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
  sharing type ZP.Z{i}.zipper = Z{i}.zipper\<close>\<close>
  sharing type ZP.M.t = M.t
end

functor Zippy_Node_Position_Mixin_Base(
    Z : ZIPPY_NODE_BASE
  ) :
  sig
    include ZIPPY_NODE_POSITION_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZP.ZPos.Z{i}.ZM.container ->
      @{AllT_args} ZP.ZDepth.Z{i}.ZM.container ->
      @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct

open Z
structure ZP = Zippy_Position_Mixin_Base(Z)
open ZP

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Fst = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  type @{AllT_args} container = @{AllT_args} ZP.Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} Z.Z{i}.ZD.content
  fun lens _ = L.lens_fst (L.id ()))
structure ZCore_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Fst
  structure L2 = Z.ZCore_Co{i})\<close>\<close>

end
