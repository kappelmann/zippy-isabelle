(*  Title:      Zippy/zippy_instance_tactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_TACTIC =
sig
  include ZIPPY_INSTANCE_CRESULTS

  structure Tac_AAM : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN
  sharing type Tac_AAM.Tac.GPU.GCS.gcpos = Base_Data.GCS.gcpos
  sharing type Tac_AAM.Tac.GPU.GCS.gclusters = Base_Data.GCS.gclusters
  sharing type Tac_AAM.Tac.GPU.F.focus = Base_Data.GFocus.focus
  sharing type Tac_AAM.Meta.Meta.metadata = Base_Data.AAMeta.metadata
  sharing type Tac_AAM.Meta.L.container = ZLP.Z5.zipper

  structure Tac :
  sig
    val ztactic_resultsq : Tac_AAM.ztactic -> @{AllT_args} ZLP.Z2.zipper -> Tac_AAM.result Seq.seq

    type @{AllT_args} data = {
      meta : Base_Data.AMeta.metadata,
      empty_action : int -> @{AllT_args} Base_Data.CAction.action,
      result_action : Result_Action.result -> @{AllT_args} Base_Data.CAction.action,
      cresultsq : @{AllT_args} CResults.cresultsq,
      tac : (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph}

    val cresults_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} data ->
      @{AllT_args} CResults.data
    val caction_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} data ->
      @{AllT_args} CAction.data
    val cons_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} data ->
      Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLP.Z3.zipper,
        @{AllT_args} ZLP.Z4.zipper) morph
    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper option) morph
  end
end

functor Zippy_Instance_Tactic(
    structure Z : ZIPPY_INSTANCE_CRESULTS
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_CAction : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_TACTIC =
struct
open Z; open ZLP MU
structure GCluster = Zippy_Goal_Cluster_Mixin(Mixin_Base2.GCluster)
structure CAction_More = Zippy_CAction_Mixin(
  structure CAction = Mixin_Base4.CAction
  structure Exn = Exn; structure Ctxt = Ctxt; structure Log = Log_CAction
  structure Show = Show.Zipper4)
structure CResults_More = Zippy_CResults_Mixin(CResults)

structure Tac_AAM = Zippy_Tactic_Action_App_Metadata_Mixin(
  Zippy_Tactic_Action_App_Metadata_Mixin_Base(
    structure Meta = Zippy_Action_App_Metadata_Mixin_Base(
      structure Meta = Base_Data.AAMeta; structure L = Lens5.Meta)
    structure Tac = Zippy_ZTactic(
      structure R = Base_Data.Tac_Res; structure RTac = Standard_Zippy_RTactic)))

structure Tac =
struct
fun ztactic_resultsq tac z2 = tac (GCluster.get_state z2)

local open Base_Data
in
type @{AllT_args} data = {
  meta : AMeta.metadata,
  empty_action : int -> @{AllT_args} CAction.action,
  result_action : CResults.result -> @{AllT_args} CAction.action,
  cresultsq : @{AllT_args} CResults.cresultsq,
  tac : (@{ParaT_args} GFocus.focus, Tac_AAM.ztactic) morph}
end

local open SC Mo A
in
fun cresults_from_data exn {cresultsq, tac,...} focus = Up4.morph >>> Up3.morph
  >>> (fn z2 => tac focus
  >>= arr (fn tac => ztactic_resultsq tac z2 |> CResults_More.cresults_from_resultsq exn cresultsq))

fun cresults_data_from_data exn (data as {meta, result_action, empty_action,...}) =
  {meta = meta, empty_action = empty_action, result_action = result_action,
    cresults = cresults_from_data exn data}

fun caction_data_from_data exn = cresults_data_from_data exn #> CResults.caction_data_from_data

fun cons_action x = caction_data_from_data x #> Z.CAction.cons_action

fun cons_action_cluster exn meta =
  List.map (apsnd (fn data => fn focus => cons_action exn data focus >>> Up4.morph))
  #> Node.cons3 exn meta
end
end
end
