(*  Title:      Zippy/alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "LINKED_ZIPPER"\<close>

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

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MOVES"\<close>
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

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper" {i}]\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Z{j}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.Z{j}.ZM.container
    where type @{AllT_args} Z{j}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.Z{j}.ZD.content
    where type @{AllT_args} Z{j}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.Z{j}.ZD.zcontext
    where type @{AllT_args} Z{j}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.Z{j}.zipper\<close>\<close>
  = Z\<close>\<close>
