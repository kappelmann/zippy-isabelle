(*  Title:      Zippy/pair_morph.ML
    Author:     Kevin Kappelmann

Note: this could be generalised to dependent pairings where the input of the second morphism depends
on the input/output of the first. In the context of Zippy, this could be used to adjoin content
and positional dependent information to an existing zipper, such as the sum of costs up to the
focused node (as needed for an A^* algorithm), for free.
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_MORPH"\<close> =
sig
  structure M1 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  structure M2 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type M1.M.t = M2.M.t

  include \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  where type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
  where type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to
  sharing type M.t = M1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Morph"\<close>(
    structure M1 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    structure M2 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    sharing type M2.M.t = M1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_MORPH"\<close>
  =
struct
structure M1 = M1
structure M2 = M2

structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = M1
open M

type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to

fun morph x = x |> M1.K.*** (M1.morph, M2.morph)
end
