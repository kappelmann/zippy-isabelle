(*  Title:      HOCLP/alternating_position_zippers.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_POSITION_ZIPPERS"\<close> =
sig
  structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "POSITION_ZIPPER"\<close>
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{T_args} A.N{i}.content = @{T_args} Z.ZO.content
  where type @{T_args} A.Z{i}.ZM.container = @{T_args} Z.ZM.container
  where type @{T_args} A.Z{i}.ZO.zcontext = @{T_args} Z.ZO.zcontext
  where type @{T_args} A.Z{i}.zipper = @{T_args} Z.zipper\<close>\<close>
  where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Position_Zippers"\<close>(
    Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "POSITION_ZIPPER"\<close>
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_POSITION_ZIPPERS"\<close> =
struct
structure Z = Z
structure AZN = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes"\<close>(
  structure A = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes_Base_Args_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} = Z
    type @{T_args} ncontent{i} = @{T_args} Z{i}.ZO.content
    fun ncontent{i} x = Z.id () x
    fun next{i} _ = Z.M.pure (Z.M.pure ())
    fun content{i} x _ = Z.M.pure x
    \<close>\<close>)
  structure ZD = Zipper_Data)
open AZN
end