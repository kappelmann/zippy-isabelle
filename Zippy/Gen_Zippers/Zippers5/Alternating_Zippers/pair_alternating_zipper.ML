(*  Title:    HOCLP/pair_alternating_zipper.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close> =
sig
  structure AZ1 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  structure AZ2 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  sharing type AZ2.M.t = AZ1.M.t

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container =
    @{AllT_args} AZ1.Z{i}.ZM.container * @{AllT_args} AZ2.Z{i}.ZM.container
  where type @{AllT_args} Z{i}.ZO.content =
    @{AllT_args} AZ1.Z{i}.ZO.content * @{AllT_args} AZ2.Z{i}.ZO.content
  where type @{AllT_args} Z{i}.ZO.zcontext =
    @{AllT_args} AZ1.Z{i}.ZO.zcontext * @{AllT_args} AZ2.Z{i}.ZO.zcontext
  where type @{AllT_args} Z{i}.zipper =
    @{AllT_args} AZ1.Z{i}.zipper * @{AllT_args} AZ2.Z{i}.zipper
  where type (@{ParaT_args} 'a) Z{i}.M.t = (@{ParaT_args} 'a) AZ1.Z{i}.M.t\<close>\<close>
end

functor \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure AZ1 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    structure AZ2 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    sharing type AZ2.M.t = AZ1.M.t
    sharing type AZ2.L.lens = AZ1.L.lens
  ) : \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close>
  =
struct

structure AZ1 = AZ1
structure AZ2 = AZ2
structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = AZ1
open M
structure L = AZ1.L

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Pair_Zipper"\<close>(
  structure Z1 = AZ1.Z{i}
  structure Z2 = AZ2.Z{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = AZ1.Down{i}
  structure M2 = AZ2.Down{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = \<^eval>\<open>sfx_T_nargs "Pair_Move"\<close>(
  structure M1 = AZ1.Up{i}
  structure M2 = AZ2.Up{i}
)\<close>\<close>

end
