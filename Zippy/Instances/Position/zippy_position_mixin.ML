(*  Title:      Zippy/zippy_position_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_POSITION_MIXIN =
sig
  include ZIPPY_POSITION_MIXIN_BASE

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZZPos_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZPos_Co{i}.data
  sharing type ZZPos_Co{i}.container = Z{i}.zipper

  structure ZZDepth_Co{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZDepth_Co{i}.data
  sharing type ZZDepth_Co{i}.container = Z{i}.zipper\<close>\<close>
end

functor Zippy_Position_Mixin(
    Z : ZIPPY_POSITION_MIXIN_BASE
  ) : ZIPPY_POSITION_MIXIN =
struct

open Z

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZZPos_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = ZPos_Co{i})

structure ZZDepth_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = ZDepth_Co{i})\<close>\<close>

end
