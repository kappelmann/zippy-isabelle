(*  Title:      Zippy/linked_zipper.ML
    Author:     Kevin Kappelmann
*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
signature \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
  sharing type L.K.M.t = M.t
  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Z{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{j}.ZD.L.lens = L.lens
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
  sharing type Up{j}.to =  Z\<^eval>\<open>string_of_int ({j} - 1) ^ "."\<close>zipper
  sharing type Up{j}.M.t = M.t\<close>
  where start = 2 and stop = {i}\<close>
end

functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Zipper"]\<close>(
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER_MOVES"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    structure ZD{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD{j}.zipper = Z.Z{j}.zipper
    sharing type ZD{j}.L.lens = ZD1.L.lens
    sharing type ZD{j}.L.K.M.t = Z.M.t\<close>
    where stop = {i}\<close>
  ) : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
struct

open Z
structure L = ZD1.L
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Z{j} = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(structure ZM = Z.Z{j}; structure ZD = ZD{j})\<close>
where stop = {i}\<close>

end\<close>
where start = 2\<close>
