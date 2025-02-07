(*  Title:      HOCLP/alternating_zippers.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close> =
sig
  include MOVE_BASE
  structure L : LENS
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) cat
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  sharing type Z{i}.ZO.L.lens = L.lens
  sharing type Z{i}.M.t = M.t\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  where type @{T_args} from = @{T_args} Z{i}.zipper
  where type @{T_args} to = @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  where type @{T_args} from = @{T_args} Z{i}.zipper
  where type @{T_args} to = @{T_args} Z\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>\<close>
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers"\<close>(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_MOVES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure ZO{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.Z{i}.cat
    sharing type ZO{i}.zipper = Z.Z{i}.zipper
    sharing type ZO{i}.L.lens = ZO1.L.lens\<close>\<close>
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close> =
struct

open Z
structure L = ZO1.L
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZM = Z.Z{i}; structure ZO = ZO{i}
)\<close>\<close>

end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{T_args} Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{T_args} Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{T_args} Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  = Z
