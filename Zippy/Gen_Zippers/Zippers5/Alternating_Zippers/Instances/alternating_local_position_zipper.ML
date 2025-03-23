(*  Title:      Zippy/alternating_local_position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close> =
sig
  structure Z : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close>
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} A.N{i}.content = @{AllT_args} Z.ZO.content
  where type @{AllT_args} A.Z{i}.ZM.container = @{AllT_args} Z.ZM.container
  where type @{AllT_args} A.Z{i}.ZO.zcontext = @{AllT_args} Z.ZO.zcontext
  where type @{AllT_args} A.Z{i}.zipper = @{AllT_args} Z.zipper\<close>\<close>
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Local_Position_Zipper"\<close>(
    Z : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close> =
struct
structure Z = Z
structure AZN = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
  structure A = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} = Z
    type @{AllT_args} ncontent{i} = @{AllT_args} Z{i}.ZO.content
    fun ncontent{i} x = Z.id () x
    fun next{i} _ = Z.M.pure (Z.M.pure ())
    fun content{i} x _ = Z.M.pure x
    \<close>\<close>)
  structure ZD = \<^eval>\<open>sfx_ParaT_nargs "Zipper_Data"\<close>)
open AZN
end
