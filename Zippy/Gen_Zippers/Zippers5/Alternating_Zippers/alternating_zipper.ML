(*  Title:      Zippy/alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "LINKED_ZIPPER"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Down{i}.from = Z{i}.zipper
  sharing type Down{i}.to = Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>
  where start = \<open>ML_Gen.nzippers ()\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Up{i}.from = Z{i}.zipper
  sharing type Up{i}.to = Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>
  where stop = 1\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MORPHS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure ZD{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD{i}.zipper = Z.Z{i}.zipper\<close>\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
struct
open Z
structure LZ = \<^eval>\<open>pfx_sfx_nargs "Linked_Zipper"\<close>(
  structure Z = Z
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZD{i} = ZD{i}\<close>\<close>)
open LZ
end
