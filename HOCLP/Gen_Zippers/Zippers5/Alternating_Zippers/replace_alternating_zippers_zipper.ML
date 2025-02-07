(*  Title:      HOCLP/replace_alternating_zippers_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Alternating_Zippers" ^ "_Zipper"\<close>(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} nzipper{i}
    val nzipper{i} : (@{ParaT_args}, @{T_args} Z.Z{i}.zipper, @{T_args} nzipper{i}) Z.cat
    val dest_nzipper{i} : (@{ParaT_args}, @{T_args} nzipper{i}, @{T_args} Z.Z{i}.zipper) Z.cat\<close>\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZO.content = @{T_args} Z.Z{i}.ZO.content
    where type @{T_args} Z{i}.ZO.zcontext = @{T_args} Z.Z{i}.ZO.zcontext
    where type @{T_args} Z{i}.ZM.container = @{T_args} Z.Z{i}.ZM.container
    where type @{T_args} Z{i}.zipper = @{T_args} nzipper{i}\<close>\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
struct

structure M : MOVE_BASE = Z
open M
structure L = Z.L

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Zipper"\<close>(
  structure Z = Z.Z{i}
  type @{T_args} nzipper = @{T_args} nzipper{i}
  val nzipper = nzipper{i}
  val dest_nzipper = dest_nzipper{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
  structure M = Z.Down{i}
  type @{T_args} nfrom = @{T_args} nzipper{i}
  type @{T_args} nto = @{T_args} nzipper\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>
  val dest_nfrom = dest_nzipper{i}
  val nto = nzipper\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Move" ^ "_From_To"\<close>(
  structure M = Z.Up{i}
  type @{T_args} nfrom = @{T_args} nzipper{i}
  type @{T_args} nto = @{T_args} nzipper\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i}\<close>
  val dest_nfrom = dest_nzipper{i}
  val nto = nzipper\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i}\<close>
)\<close>\<close>

end