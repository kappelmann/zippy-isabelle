(*  Title:      Zippy/zippy_position_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_POSITION_MIXIN =
sig
  include ZIPPY_POSITION_MIXIN_BASE

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZZPOS_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZPOS_CO{i}.data
  sharing type ZZPOS_CO{i}.container = Z{i}.zipper
  sharing type ZZPOS_CO{i}.K.M.t = M.t
  sharing type ZZPOS_CO{i}.lens = L.lens

  structure ZZDEPTH_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZDEPTH_CO{i}.data
  sharing type ZZDEPTH_CO{i}.container = Z{i}.zipper
  sharing type ZZDEPTH_CO{i}.K.M.t = M.t
  sharing type ZZDEPTH_CO{i}.lens = L.lens\<close>\<close>
end

functor Zippy_Position_Mixin(
    Z : ZIPPY_POSITION_MIXIN_BASE
  ) : ZIPPY_POSITION_MIXIN =
struct

open Z

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZZPOS_CO{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.CO
  structure L2 = ZPOS_CO{i})

structure ZZDEPTH_CO{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.CO
  structure L2 = ZDEPTH_CO{i})\<close>\<close>

end
