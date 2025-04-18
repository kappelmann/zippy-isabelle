(*  Title:      Zippy/zippy_thm_state.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_THM_STATE =
sig
  type state = thm
  val pretty : Proof.context -> state -> Pretty.T
  val init : cterm -> state
  val get_thm : state -> thm
  val nprems_of : state -> int

  val is_finished : state -> bool

  val mk_conj : int -> state -> state
  val unmk_conj : int -> state -> state

  val protect_prems : state -> state
  val unprotect_prems : state -> state
end

structure Zippy_Thm_State : ZIPPY_THM_STATE =
struct

type state = thm

val pretty = Thm.pretty_thm
val init = Goal.init
val get_thm = Goal.conclude
val nprems_of = Thm.nprems_of

val is_finished = Thm.no_prems

val mk_conj = Conjunction.uncurry_balanced
val unmk_conj = Conjunction.curry_balanced

val protect_conv = Conv.rewr_conv @{thm Pure.prop_def[symmetric]}
val unprotect_conv = Conv.rewr_conv @{thm Pure.prop_def}
val protect_prems_conv = Conversion_Util.imp_conv protect_conv Conv.all_conv
val unprotect_prems_conv = Conversion_Util.imp_conv unprotect_conv Conv.all_conv
val unprotect_prems = Conv.fconv_rule unprotect_prems_conv
val protect_prems = Conv.fconv_rule protect_prems_conv

end
