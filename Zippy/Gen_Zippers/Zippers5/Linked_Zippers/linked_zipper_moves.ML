(*  Title:      Zippy/linked_zipper_moves.ML
    Author:     Kevin Kappelmann
*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
signature \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER_MOVES"]\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Z{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  sharing type Z{j}.M.t = M.t\<close>
  where stop = {i}\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Down{j} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Down{j}.from = Z{j}.zipper
  sharing type Down{j}.to = Z\<^eval>\<open>string_of_int ({j} + 1) ^ "."\<close>zipper
  sharing type Down{j}.M.t = M.t\<close>
  where stop = \<open>{i} - 1\<close>\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Up{j} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Up{j}.from = Z{j}.zipper
  sharing type Up{j}.to = Z\<^eval>\<open>string_of_int ({j} - 1) ^ "."\<close>zipper
  sharing type Up{j}.M.t = M.t\<close>
  where start = 2 and stop = {i}\<close>
end\<close>
where start = 2\<close>
