(*  Title:      Zippy/morph.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "MORPH"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} from
  type @{AllT_args} to
  val morph : (@{ParaT_args} @{AllT_args} from, @{AllT_args} to) morph
end

(*endo morphism*)
signature \<^eval>\<open>sfx_T_nargs "EMORPH"\<close> =
sig
  include \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type from = to
end

functor \<^eval>\<open>sfx_T_nargs "EMorph"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} data
    val morph : (@{ParaT_args} @{AllT_args} data) M.emorph
  ) : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close> =
struct
open M
type @{AllT_args} from = @{AllT_args} data
type @{AllT_args} to = @{AllT_args} data
val morph = morph
end
