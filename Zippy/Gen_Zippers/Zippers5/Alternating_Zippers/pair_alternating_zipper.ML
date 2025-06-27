(*  Title:    Zippy/pair_alternating_zipper.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close> =
sig
  structure SZ1 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  structure SZ2 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZ2.Z.Z{i}.zipper = SZ1.Z.Z{i}.zipper
  sharing type SZ2.Z.Z{i}.ZM.container = SZ1.Z.Z{i}.ZM.container
  sharing type SZ2.Z.Z{i}.ZD.content = SZ1.Z.Z{i}.ZD.content
  sharing type SZ2.Z.Z{i}.ZD.zcontext = SZ1.Z.Z{i}.ZD.zcontext\<close>\<close>
  sharing type SZ2.Z.M.t = SZ1.Z.M.t

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.container * @{AllT_args} SZ2.ZSub.Z{i}.ZM.container
  where type @{AllT_args} Z{i}.ZD.content =
    @{AllT_args} SZ1.ZSub.Z{i}.ZD.content * @{AllT_args} SZ2.ZSub.Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext =
    @{AllT_args} SZ1.ZSub.Z{i}.ZD.zcontext * @{AllT_args} SZ2.ZSub.Z{i}.ZD.zcontext
  where type @{AllT_args} Z{i}.zipper =
    @{AllT_args} SZ1.ZSub.Z{i}.zipper * @{AllT_args} SZ2.ZSub.Z{i}.zipper\<close>\<close>
  sharing type M.t = SZ1.Z.M.t
end

functor \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure AZ1 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    structure AZ2 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    sharing type AZ2.M.t = AZ1.M.t
  ) : \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close>
  =
struct

structure Z =
struct
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = AZ1
  open M
  structure L = AZ1.L
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} = \<^eval>\<open>sfx_T_nargs "Pair_Zipper"\<close>(
    structure Z1 = AZ1.Z{i}
    structure Z2 = AZ2.Z{i})

  structure Down{i} = \<^eval>\<open>sfx_T_nargs "Pair_Morph"\<close>(
    structure M1 = AZ1.Down{i}
    structure M2 = AZ2.Down{i})

  structure Up{i} = \<^eval>\<open>sfx_T_nargs "Pair_Morph"\<close>(
    structure M1 = AZ1.Up{i}
    structure M2 = AZ2.Up{i})\<close>\<close>
end
open Z
structure SZ1 =
struct
  structure Z = Z
  structure ZSub = AZ1
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} = Z{i}.SZ1\<close>\<close>
end
structure SZ2 =
struct
  structure Z = Z
  structure ZSub = AZ2
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} = Z{i}.SZ2\<close>\<close>
end
end
