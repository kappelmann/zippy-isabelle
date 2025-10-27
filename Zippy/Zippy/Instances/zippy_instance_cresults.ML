(*  Title:      Zippy/zippy_instance_cresults.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_CRESULTS =
sig
  include ZIPPY_INSTANCE_CACTION

  structure CResults :
  sig
    include ZIPPY_CRESULTS_MIXIN_BASE
    where type result = Result_Action.result
    where type @{AllT_args} zipper = @{AllT_args} ZLP.Z4.zipper
    where type cost = Base_Data.CAction.cost
    where type (@{ParaT_args} 'a, 'b, 'c) Co.Co.acoroutine =
      (@{ParaT_args} 'a, 'b, 'c) Co.Co.acoroutine
    where type @{ParaT_args encl: "(" ")"} Co.ME.exn = @{ParaT_args encl: "(" ")"} Exn.ME.exn
    where type (@{ParaT_args} 'a) Co.M.t = (@{ParaT_args} 'a) M.t

    val caction : (int -> @{AllT_args} Base_Data.CAction.action) ->
      (result -> @{AllT_args} Base_Data.CAction.action) ->
      @{AllT_args} cresults -> @{AllT_args} Base_Data.CAction.caction

    (*updates with passed caction data if no successful action applications have been made;
    otherwise returns passed action*)
    val orelse_update_action : @{AllT_args} Base_Data.CAction.action -> @{AllT_args} CAction.data ->
      int -> @{AllT_args} Base_Data.CAction.action

    type @{AllT_args} data = {
      meta : Base_Data.AMeta.metadata,
      (*first argument is the number of successful action applications before the empty action*)
      empty_action : int -> @{AllT_args} Base_Data.CAction.action,
      result_action : result -> @{AllT_args} Base_Data.CAction.action,
      cresults : Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLP.Z4.zipper,
        @{AllT_args} cresults) morph}

    val caction_data_from_data : @{AllT_args} data -> @{AllT_args} CAction.data
    val cons_action : @{AllT_args} data -> Base_Data.GFocus.focus ->
      (@{ParaT_args} @{AllT_args} ZLP.Z3.zipper, @{AllT_args} ZLP.Z4.zipper) morph
    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper option) morph

    (* cost *)
    val enum_double_cresultsq : cost -> @{AllT_args} cresultsq
    val with_double_cost_depth_cresultsq : @{AllT_args} cresultsq -> @{AllT_args} cresultsq
    (*doubles the cost with each pull of a result*)
    val enum_double_cost_depth_cresultsq : (@{ParaT_args} cost) emorph -> cost -> @{AllT_args} cresultsq
    val enum_double_cost_double_cost_depth_cresultsq : cost -> @{AllT_args} cresultsq
  end
end

functor Zippy_Instance_CResults(
    structure Z : ZIPPY_INSTANCE_CACTION
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_CAction : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_CAction_CResults : ZIPPY_LOGGER_MIXIN_BASE
    val double : Z.Base_Data.CAction.cost -> Z.Base_Data.CAction.cost
  ) : ZIPPY_INSTANCE_CRESULTS =
struct

open Z; open ZLP MU
structure ZP = Zippy_Positions_Mixin(structure Z = ZP; structure Exn = Exn)

structure CResults = Zippy_CResults_Mixin(Zippy_CResults_Mixin_Base(
  structure M = ZLP
  structure Co = Co
  type @{AllT_args} zipper = @{AllT_args} Z4.zipper
  type cost = Base_Data.CAction.cost
  type result = Base_Data.AAMeta.metadata Base_Data.Tac_Res.result
  type @{AllT_args} cresults = (@{ParaT_args} @{AllT_args} zipper, cost, result) Co.Co.acoroutine
  val cresults = I; val dest_cresults = I))

structure CAction_More = Mixin_Base4.CAction
structure CAction_CResults = Zippy_CAction_CResults_Mixin(
  structure CAction_CResults = Zippy_CAction_CResults_Mixin_Base(
    structure CResults = CResults; structure CAction = Base_Data.CAction)
  structure Ctxt = Ctxt
  structure Show_CAction_Zipper = Show.Zipper4
  structure Log_CAction = Log_CAction; structure Log = Log_CAction_CResults)
structure CResults_Pos = Zippy_CResults_Positions_Mixin(
  structure Z = ZP; structure CResults = CResults)
structure Action_App_Num = Zippy_Action_App_Num_Mixin(Mixin_Base4.Action_App_Num)

structure CResults =
struct open CResults

local open A Mo SC
in
fun caction empty_action = CAction_CResults.caction_from_cresults empty_action
  (fn _ => fn _ => arr Action_App_Num.inc_action_app_num)

fun orelse_update_action action update_data counter = if counter = 0
  then CAction.update_action update_data else action

local open Base_Data
in
type @{AllT_args} data = {
  meta : AMeta.metadata,
  empty_action : int -> @{AllT_args} CAction.action,
  result_action : result -> @{AllT_args} CAction.action,
  cresults : GFocus.focus -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} cresults) morph}
end

fun caction_from_data {empty_action, result_action, cresults,...} focus =
  (fn z4 => cresults focus z4 >>= (caction empty_action result_action
    #> Mixin_Base4.CAction.run_caction #> (fn caction => caction z4)))
  |> Mixin_Base4.CAction.caction

fun caction_data_from_data (data as {meta,...}) = {meta = meta, caction = caction_from_data data}

fun cons_action x = caction_data_from_data x |> Z.CAction.cons_action

fun cons_action_cluster exn meta =
  List.map (apsnd (fn data => fn focus => cons_action data focus >>> Up4.morph))
  #> Node.cons3 exn meta

(* cost *)
fun enum_double_cresultsq x = CResults.enum_cresultsq (arr double) x
fun with_double_cost_depth_cresultsq x = CResults_Pos.with_depth_cresultsq
  (fn i => arr (funpow i double)) x
fun enum_double_cost_depth_cresultsq next = CResults.enum_cresultsq next
  #> with_double_cost_depth_cresultsq
fun enum_double_cost_double_cost_depth_cresultsq x = enum_double_cost_depth_cresultsq (arr double) x
end
end

end