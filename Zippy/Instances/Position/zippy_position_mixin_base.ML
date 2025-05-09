(*  Title:      Zippy/zippy_position_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_POSITION_MIXIN_BASE =
sig
  include ZIPPY_BASE_BASE

  structure ZPos : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close>
  sharing type ZPos.M.t = M.t

  structure ZDepth : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close>
  sharing type ZDepth.M.t = M.t

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZPos_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZPos.Z{i}.ZD.content
  sharing type ZPos_Co{i}.container = Z{i}.ZD.content

  structure ZDepth_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZDepth.Z{i}.ZD.content
  sharing type ZDepth_Co{i}.container = Z{i}.ZD.content\<close>\<close>
end

functor Zippy_Position_Mixin_Base(
    Z : ZIPPY_BASE_BASE
  ) :
  sig
    include ZIPPY_POSITION_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZPos.Z{i}.ZM.container -> @{AllT_args} ZDepth.Z{i}.ZM.container ->
      @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct

structure ZPos = \<^eval>\<open>pfx_sfx_nargs "Alternating_Global_Position_Zipper"\<close>(Z)
structure ZDepth = \<^eval>\<open>pfx_sfx_nargs "Alternating_Depth_Zipper"\<close>(Z)

structure Z = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = Z
  structure AZ2 = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure AZ1 = ZPos
    structure AZ2 = ZDepth))

open Z

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZPos_Co{i} = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  type @{AllT_args} container = @{AllT_args} Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} ZPos.Z{i}.ZD.content
  fun lens _ = L.lens_fst (L.lens_snd (L.id ())))\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZDepth_Co{i} = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  type @{AllT_args} container = @{AllT_args} Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} ZDepth.Z{i}.ZD.content
  fun lens _ = L.lens_snd (L.lens_snd (L.id ())))\<close>\<close>

fun container p d c = (c, (p, d))
fun init_container c = container ZPos.init_path ZDepth.init_depth c
\<^imap>\<open>\<open>{i}\<close> => \<open>
val container{i} = container
val init_container{i} = init_container
\<close>\<close>

end
