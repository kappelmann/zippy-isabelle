(*  Title:      Zippy/zippy_paction_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_MIXIN =
sig
  include ZIPPY_PACTION_MIXIN_BASE
  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  val no_action : @{ParaT_args encl = "(" ")"} Exn.AE.exn -> @{AllT_args} action
  val no_paction : @{ParaT_args encl = "(" ")"} Exn.AE.exn -> @{AllT_args} paction
  val disable_paction : @{ParaT_args encl = "(" ")"} Exn.AE.exn -> @{AllT_args} zipper ->
    @{AllT_args} zipper

  val get_run_paction : (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) cat
  val run_action : prio * @{AllT_args} action -> (@{ParaT_args} @{AllT_args} zipper,
    @{AllT_args} action_result) move
end

functor Zippy_PAction_Mixin(
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = PAction.M.t
  ) : ZIPPY_PACTION_MIXIN =
struct

open PAction
structure Exn = Exn; open Exn

fun no_action e _ = AE.throw' e
fun no_paction e = AE.throw' e |> PAction.paction

fun disable_paction e = curry (L.set_modify L.modifier) (no_paction e)

fun get_run_paction x = L.getter x |> (fn paction => PAction.run_paction paction x)
fun run_action (p, action) = action p

end
