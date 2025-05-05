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
  sharing type ZP.L.lens = L.lens
end

functor Zippy_Lists_Position_Mixin_Base(
    Z : ZIPPY_LISTS_BASE
  ) : ZIPPY_LISTS_POSITION_MIXIN_BASE
  =
struct
open Z
structure Z = Zippy_Node_Position_Mixin_Base(Z)
open Z
end


