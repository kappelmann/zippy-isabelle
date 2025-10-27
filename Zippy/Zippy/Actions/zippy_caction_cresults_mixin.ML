(*  Title:      Zippy/zippy_caction_cresults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CACTION_CRESULTS_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_CACTION_CRESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = CAction.M.t

  type @{AllT_args} zipper = @{AllT_args} CAction.zipper

  val gen_caction_from_cresults :
    (*action when results are empty*)
    @{AllT_args} CAction.action ->
    (*action with pulled result and the remaining cresults*)
    (CResults.result * @{AllT_args} CResults.cresults -> @{AllT_args} CAction.action) ->
    @{AllT_args} CResults.cresults -> @{AllT_args} CAction.caction

  (*recursively sets new action using remaining cresults*)
  val caction_from_cresults :
    (*takes number of previously returned results as argument*)
    (int -> @{AllT_args} CAction.action) ->
    (*additional updates with remaining cresults*)
    (@{AllT_args} CResults.cresults -> cost -> (@{ParaT_args} @{AllT_args} zipper) emorph) ->
    (CResults.result -> @{AllT_args} CAction.action) ->
    @{AllT_args} CResults.cresults -> @{AllT_args} CAction.caction
end

functor Zippy_CAction_CResults_Mixin(
    structure CAction_CResults : ZIPPY_CACTION_CRESULTS_MIXIN_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = CAction_CResults.CAction.M.t
    structure Show_CAction_Zipper : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_CAction_Zipper.t = CAction_CResults.CAction.zipper
    structure Log_CAction : ZIPPY_LOGGER_MIXIN_BASE
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_CACTION_CRESULTS_MIXIN =
struct

open CAction_CResults Log
structure MU = Zippy_Monad_Util(CAction.M); open MU MU.MB
structure Exn = Zippy_Exception_Mixin(CResults.Co)
structure CAction = Zippy_CAction_Mixin(structure CAction = CAction; structure Exn = Exn
  structure Ctxt = Ctxt; structure Log = Log_CAction; structure Show = Show_CAction_Zipper)
structure CResults = Zippy_CResults_Mixin(CResults)

type @{AllT_args} zipper = @{AllT_args} CAction.zipper
type cost = CAction.cost

local open SC Mo A CResults.Co Exn
in
fun gen_caction_from_cresults empty_action result_tail_cresults_action cresults =
  let fun update_action rp_aco cost = AE.catch'
    (fn z => Co.resume rp_aco z
      >>= (apsnd CResults.cresults #> (fn rpress => result_tail_cresults_action rpress cost z)))
    (Ctxt.with_ctxt (fn ctxt => (@{log Logger.DEBUG} ctxt (fn _ => "CResults empty.");
      empty_action cost)))
  in CResults.run_cresults cresults >>> second (arr update_action) |> CAction.caction end

fun caction_from_cresults empty_action update_tail_cresults result_action =
  let
    fun update_tail_cresults_set_rec counter cresults cost =
      CAction.set_caction (run (counter + 1) cresults) #> update_tail_cresults cresults cost
    and result_tail_cresults_action counter (result, cresults) cost =
      update_tail_cresults_set_rec counter cresults cost >>> result_action result cost
    and run counter = gen_caction_from_cresults (empty_action counter)
      (result_tail_cresults_action counter)
  in run 0 end
end

end

