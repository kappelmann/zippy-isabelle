(*  Title:      Zippy/alternating_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MOVES"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "LINKED_ZIPPER_MOVES"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Down{i}.from = Z{i}.zipper
  sharing type Down{i}.to = Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>
  where start = \<open>ML_Gen.nzippers ()\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Up{i}.from = Z{i}.zipper
  sharing type Up{i}.to = Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>
  where stop = 1\<close>
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper_Moves" {i}]\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MOVES"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MOVES"\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Z{j}.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.Z{j}.container
    where type @{AllT_args} Z{j}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.Z{j}.zipper\<close>\<close>
  = Z\<close>\<close>
