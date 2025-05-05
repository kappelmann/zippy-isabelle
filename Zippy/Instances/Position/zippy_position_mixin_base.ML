(*  Title:      Zippy/zippy_position_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_POSITION_MIXIN_BASE =
sig
  include ZIPPY_BASE_BASE

  structure ZPOS : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close>
  sharing type ZPOS.M.t = M.t
  sharing type ZPOS.L.lens = L.lens

  structure ZDEPTH : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close>
  sharing type ZDEPTH.M.t = M.t
  sharing type ZDEPTH.L.lens = L.lens

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZPOS_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZPOS.Z{i}.ZD.content
  sharing type ZPOS_CO{i}.container = Z{i}.ZD.content
  sharing type ZPOS_CO{i}.K.M.t = M.t
  sharing type ZPOS_CO{i}.lens = L.lens

  structure ZDEPTH_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZDEPTH.Z{i}.ZD.content
  sharing type ZDEPTH_CO{i}.container = Z{i}.ZD.content
  sharing type ZDEPTH_CO{i}.K.M.t = M.t
  sharing type ZDEPTH_CO{i}.lens = L.lens\<close>\<close>
end

functor Zippy_Position_Mixin_Base(
    Z : ZIPPY_BASE_BASE
  ) : ZIPPY_POSITION_MIXIN_BASE
  =
struct

structure ZPOS = \<^eval>\<open>pfx_sfx_nargs "Alternating_Global_Position_Zipper"\<close>(Z.L)
structure ZDEPTH = \<^eval>\<open>pfx_sfx_nargs "Alternating_Depth_Zipper"\<close>(Z.L)

structure Z = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = Z
  structure AZ2 = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure AZ1 = ZPOS
    structure AZ2 = ZDEPTH))

open Z

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZPOS_CO{i} = \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
  structure L = L
  type @{AllT_args} container = @{AllT_args} Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} ZPOS.Z{i}.ZD.content
  fun lens _ = L.lens_fst (L.lens_snd (L.id ())))\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZDEPTH_CO{i} = \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
  structure L = L
  type @{AllT_args} container = @{AllT_args} Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} ZDEPTH.Z{i}.ZD.content
  fun lens _ = L.lens_snd (L.lens_snd (L.id ())))\<close>\<close>

end
