(*  Title:      HOCLP/alternating_zippers_moves.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_MOVES"\<close> =
sig
  include MOVE_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
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

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers" ^ "_Moves"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_MOVES"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_MOVES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.container
    where type @{T_args} Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  = Z

