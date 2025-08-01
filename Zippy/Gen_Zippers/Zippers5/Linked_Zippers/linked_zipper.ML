(*  Title:      Zippy/linked_zipper.ML
    Author:     Kevin Kappelmann
*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
signature \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "SLENS"\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Z{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{j}.M.t = M.t\<close>
  stop: {i}\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Down{j} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Down{j}.from = Z{j}.zipper
  sharing type Down{j}.to = Z\<^eval>\<open>string_of_int ({j} + 1) ^ "."\<close>zipper
  sharing type Down{j}.M.t = M.t\<close>
  stop: \<open>{i} - 1\<close>\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Up{j} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Up{j}.from = Z{j}.zipper
  sharing type Up{j}.to =  Z\<^eval>\<open>string_of_int ({j} - 1) ^ "."\<close>zipper
  sharing type Up{j}.M.t = M.t\<close>
  start: 2 stop: {i}\<close>
end

functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Zipper"]\<close>(
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER_MORPHS"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    structure ZD{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD{j}.zipper = Z.Z{j}.zipper\<close>
    stop: {i}\<close>
  ) : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
struct

open Z
structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Z{j} = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(structure ZM = Z.Z{j}; structure ZD = ZD{j})\<close>
stop: {i}\<close>

end\<close>
start: 2\<close>
