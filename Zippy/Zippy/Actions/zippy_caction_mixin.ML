(*  Title:      Zippy/zippy_caction_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CACTION_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_CACTION_MIXIN_BASE
  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  val no_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} action
  val no_caction : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} caction

  val set_caction : @{AllT_args} caction -> @{AllT_args} zipper -> @{AllT_args} zipper

  val disable_caction : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
    (@{ParaT_args} @{AllT_args} zipper) emorph

  val get_run_caction : (@{ParaT_args} @{AllT_args} zipper, cost * @{AllT_args} action) morph
  val run_action : cost * @{AllT_args} action -> (@{ParaT_args} @{AllT_args} zipper,
    @{AllT_args} action_result) morph
end

functor Zippy_CAction_Mixin(
    structure CAction : ZIPPY_CACTION_MIXIN_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = CAction.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = CAction.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Show : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show.t = CAction.zipper
  ) : ZIPPY_CACTION_MIXIN =
struct

open CAction Log
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Exn; open Exn

fun no_action exn _ = AE.throw' exn
fun no_caction exn = AE.throw' exn |> CAction.caction

local open Mo SC A
in
fun set_caction caction z = L.set_modify L.modifier (caction, z)

fun disable_caction exn z = Ctxt.get_ctxt () >>= arr (fn ctxt =>
  (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Disabling caction of",
      Show.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
  set_caction (no_caction exn) z))

fun get_run_caction z = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Running caction of",
      Show.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
  L.getter z |> (fn caction => CAction.run_caction caction z)))

fun run_action (p, action) z = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Running action of",
      Show.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
  action p z))
end
end
