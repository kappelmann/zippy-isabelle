(*  Title:    HOCLP/pair_alternating_zippers.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ALTERNATING_ZIPPERS"\<close> =
sig
  structure AZ1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  structure AZ2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  sharing type AZ2.M.t = AZ1.M.t

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  where type @{T_args} Z1.ZM.container =
    @{T_args} AZ1.Z1.ZM.container * @{T_args} AZ2.Z1.ZM.container
  where type @{T_args} Z1.ZO.content = @{T_args} AZ1.Z1.ZO.content * @{T_args} AZ2.Z1.ZO.content
  where type @{T_args} Z1.ZO.zcontext = @{T_args} AZ1.Z1.ZO.zcontext * @{T_args} AZ2.Z1.ZO.zcontext
  where type @{T_args} Z1.zipper = @{T_args} AZ1.Z1.zipper * @{T_args} AZ2.Z1.zipper
  where type ('p1, 'a) Z1.M.t = ('p1, 'a) AZ1.Z1.M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Alternating_Zippers"\<close>(
    structure AZ1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    structure AZ2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    sharing type AZ2.M.t = AZ1.M.t
    sharing type AZ2.L.lens = AZ1.L.lens
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "PAIR_ALTERNATING_ZIPPERS"\<close>
  =
struct

structure AZ1 = AZ1
structure AZ2 = AZ2
structure M : MOVE_BASE = AZ1
open M
structure L = AZ1.L

structure Z1 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper"\<close>(
  structure Z1 = AZ1.Z1
  structure Z2 = AZ2.Z1
)

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Zipper"\<close>(
  structure Z1 = AZ1.Z{i}
  structure Z2 = AZ2.Z{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = AZ1.Down{i}
  structure M2 = AZ2.Down{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Move"\<close>(
  structure M1 = AZ1.Up{i}
  structure M2 = AZ2.Up{i}
)\<close>\<close>

end
