(*  Title:      HOCLP/rotate_alternating_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Rotate_Alternating_Zippers"\<close>(
    Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  ) :
  \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{T_args} Z{i}.ZO.content =
    @{T_args} Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZO.content
  where type @{T_args} Z{i}.ZO.zcontext =
    @{T_args} Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZO.zcontext
  where type @{T_args} Z{i}.ZM.container =
    @{T_args} Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container
  where type @{T_args} Z{i}.zipper =
    @{T_args} Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>zipper\<close>\<close>
  where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
struct
structure M : MOVE_BASE = Z
open M
structure L = Z.L
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = Z.Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>
structure Down{i} = Z.Down\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>
structure Up{i} = Z.Up\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>
\<close>\<close>
end
