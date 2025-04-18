(*  Title:      Zippy/linked_zipper.ML
    Author:     Kevin Kappelmann
*)

\<^imap>\<open>\<open>{j}\<close> => \<open>
signature \<^eval>\<open>mk_name [ML_Gen.nprefix "{j}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{i}.ZO.L.lens = L.lens
  sharing type Z{i}.M.t = M.t\<close>
  where stop = {j}\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  where type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  where type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>string_of_int ({i} + 1) ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>
  where stop = \<open>{j} - 1\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  where type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  where type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>string_of_int ({i} - 1) ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>
  where start = 2 and stop = {j}\<close>
end

functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{j}", sfx_T_nargs "Linked_Zipper"]\<close>(
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{j}", sfx_T_nargs "LINKED_ZIPPER_MOVES"]\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure ZO{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) Z.Z{i}.cat
    sharing type ZO{i}.zipper = Z.Z{i}.zipper
    sharing type ZO{i}.L.lens = ZO1.L.lens\<close>
    where stop = {j}\<close>
  ) : \<^eval>\<open>mk_name [ML_Gen.nprefix "{j}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
struct

open Z
structure L = ZO1.L
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = Z.Z{i}; structure ZO = ZO{i}
)\<close>
where stop = {j}\<close>

end

functor \<^eval>\<open>mk_name ["Instantiate", ML_Gen.nprefix "{j}", sfx_T_nargs "Linked_Zipper"]\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{j}", sfx_T_nargs "LINKED_ZIPPER"]\<close>
  ) :
    \<^eval>\<open>mk_name [ML_Gen.nprefix "{j}", sfx_T_nargs "LINKED_ZIPPER"]\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{AllT_args} Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>
    where stop = {j}\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  = Z\<close>
where start = 2\<close>
