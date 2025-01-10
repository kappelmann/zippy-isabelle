(*  Title:      HOCLP/zippy_thm_state.ML
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

end
