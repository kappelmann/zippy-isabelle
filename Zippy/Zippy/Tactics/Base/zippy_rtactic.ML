(*  Title:      Zippy/zippy_rtactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RTACTIC =
sig
  include ZIPPY_RTACTIC_RESULT
  (*standard Isabelle tactic, equal to state -> state Seq.seq*)
  type tactic = Tactical.tactic
  (*generalised result tactic*)
  type 'm rtactic = state -> 'm result Seq.seq

  (*creates missing data from input and result state*)
  val lift_tac : (state * state -> 'm) -> tactic -> 'm rtactic
  val lift_tac' : (state * state -> 'm) -> ('a -> tactic) -> 'a -> 'm rtactic

  val no_tac : 'm rtactic
end

functor Zippy_RTactic(R : ZIPPY_RTACTIC_RESULT) : ZIPPY_RTACTIC =
struct

open R

type tactic = Tactical.tactic
type 'm rtactic = state -> 'm result Seq.seq

fun lift_tac f tac state = tac state |> Seq.map (fn state' => result (f (state, state')) state')
fun lift_tac' f tac i = lift_tac f (tac i)

fun no_tac _ = Seq.empty

end

structure Standard_Zippy_RTactic = Zippy_RTactic(Zippy_RTactic_Result)