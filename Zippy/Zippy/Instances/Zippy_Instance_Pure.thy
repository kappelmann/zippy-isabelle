\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Pure
  imports
    Zippy_Instance
    Zippy_Runs
begin

text \<open>Setup the standard Zippy instance.\<close>

ML\<open>
(* create monad *)
local
  (** exceptions **)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))

  (** proof context **)
  structure Ctxt_MSTrans = \<^eval>\<open>sfx_ParaT_nargs "State_Trans"\<close>(
    type s = Proof.context; structure M = ME; structure SR = Pair_State_Result_Base)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_State_Trans"\<close>(
    structure M = ME; structure S = Ctxt_MSTrans)

  (** arbitrary state (not needed for now) **)
  (* structure MS = \<^eval>\<open>sfx_ParaT_nargs "IState_Trans"\<close>(
    structure M = Ctxt_MSTrans; structure SR = Pair_State_Result_Base)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "IMonad_Exception_State_Trans"\<close>(
    structure M = ME; structure S = MS)
  structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close> =
  struct open ME; type (@{ParaT_args} 'a) t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) t end
  structure MCtxt = \<^eval>\<open>sfx_ParaT_nargs "IMonad_State_State_Trans"\<close>(
    type ParaT = unit; structure M = Ctxt_MSTrans; structure S = ME) *)

  structure Ctxt = Zippy_Ctxt_State_Mixin(Zippy_Ctxt_State_Mixin_Base(Ctxt_MSTrans))

  (** compatibility to extract sequences from monad **)
  structure Seq_From_Monad = Zippy_Seq_From_Monad_Mixin_Base(structure M = ME
    type @{AllT_args} state = {ctxt : Proof.context(*, state : @{ParaT_arg 0}*)}
    fun seq_from_monad {ctxt(*, state*)} m = Seq.make (fn _ =>
      (*State_MSTrans.eval state m |>*) Ctxt_MSTrans.eval ctxt m |> the_default Seq.empty
      |> Seq.pull))

(* instance and utilities *)
  val exn : @{ParaT_args encl: "(" ")"} ME.exn = ()
  structure Zippy_Base = Zippy_Instance_Base(structure ME = ME
    type cost = Cost.cost
    fun update_cost c NONE = c
      | update_cost c (SOME (c', _)) = Cost.add (c, c'))
  structure Logging =
  struct
    val logger = Logger.setup_new_logger zippy_base_logger "Zippy"
    local structure Shared = struct val parent_logger = logger end
    in
    structure Base = Zippy_Logger_Mixin_Base(open Shared; val name = "Base")
    structure Copy = Zippy_Logger_Mixin_Base(open Shared; val name = "Copy")
    structure Enum_Copy = Zippy_Logger_Mixin_Base(open Shared; val name = "Enum_Copy")
    structure CAction = Zippy_Logger_Mixin_Base(open Shared; val name = "CAction")
    structure LGoals = Zippy_Logger_Mixin_Base(open Shared; val name = "LGoals")
    structure LGoals_Pos_Copy = Zippy_Logger_Mixin_Base(open Shared; val name = "LGoals_Pos_Copy")
    structure CAction_CResults = Zippy_Logger_Mixin_Base(open Shared; val name = "CAction_CResults")
    structure Result_Action = Zippy_Logger_Mixin_Base(open Shared; val name = "Result_Action")
    end
  end
  structure Zippy = Zippy_Instance(
    structure Z = Zippy_Base; structure Ctxt = Ctxt; structure Log_Base = Logging.Base
    structure Log_LGoals = Logging.LGoals; structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy
    structure Show_Cost = Zippy_Show_Mixin_Base(
      type @{AllT_args} t = Cost.cost
      val pretty = Library.K Cost.pretty))
  structure Zippy_CAction = Zippy_Instance_CAction(
    structure Z = Zippy
    val mk_exn = Library.K exn
    structure Ctxt = Ctxt; structure Log_Base = Logging.Base;
    structure Log_CAction = Logging.CAction; structure Log_Result_Action = Logging.Result_Action
    structure Log_LGoals = Logging.LGoals; structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy
    structure Log_Copy = Logging.Copy; structure Log_Enum_Copy = Logging.Enum_Copy)
  structure Zippy_CResults = Zippy_Instance_CResults(
    structure Z = Zippy_CAction
    val double = Cost.double
    structure Ctxt = Ctxt; structure Log_CAction = Logging.CAction
    structure Log_CAction_CResults = Logging.CAction_CResults)
  structure Zippy_Tactic = Zippy_Instance_Tactic(
    structure Z = Zippy_CResults; structure Ctxt = Ctxt; structure Log_CAction = Logging.CAction)
in
(* final creation of structure *)
structure Zippy =
struct
open Zippy_Base Zippy Zippy_CAction Zippy_CResults Zippy_Tactic
(** add loggers **)
structure Logging = Logging
(** add monads and cost **)
(* structure State_MSTrans = MS
structure State = Zippy_State_Mixin(Zippy_State_Mixin_Base(MS)) *)
structure Ctxt_MSTrans = Ctxt_MSTrans
structure Ctxt = Ctxt
structure Seq_From_Monad = Seq_From_Monad
structure Cost = Cost
(** add compound mixins **)
local
  structure Base_Mixins = struct structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt end
  structure Goals = Zippy_Goals_Mixin_Base(
    structure GClusters = Mixin_Base1.GClusters; structure GCluster = Mixin_Base2.GCluster)
  structure Goals_Pos = Zippy_Goals_Pos_Mixin(structure Z = ZLPC
    structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU))
  structure Goals_Pos_Copy = Zippy_Goals_Pos_Copy_Mixin(Zippy_Goals_Pos_Copy_Mixin_Base(open Goals_Pos
    structure Copy = Mixin_Base3.Copy))
in
structure ZB = Zippy_Base(open Base_Mixins; structure Z = ZLPC; structure Log = Logging.Base
  \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
structure ZL = Zippy_Lists(open Base_Mixins; structure Z = ZLPC)
structure LGoals_Pos_Copy = Zippy_Lists_Goals_Pos_Copy_Mixin(open Base_Mixins; structure Z = ZL
  structure GPC = Goals_Pos_Copy;
  structure Log = Logging.LGoals_Pos_Copy; structure Log_Base = Logging.Base;
  structure Log_LGoals = Logging.LGoals; \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
end
(** add instance specific utilities **)
structure Util =
struct
  val exn = exn
  local
    open ZLPC
    structure ZN = Zippy_Node(structure Z = ZLPC; structure Exn = Exn)
    structure ZL = Zippy_Lists(structure Z = ZLPC; structure Co = Co)
    structure Goals = Zippy_Goals_Mixin_Base(
      structure GClusters = Mixin_Base1.GClusters; structure GCluster = Mixin_Base2.GCluster)
    structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = ZL; structure Goals = Goals
      structure Ctxt = Ctxt; structure Log = Logging.LGoals)
    fun node_no_next1 gclusters = ZN.node_no_next1 exn (Node.co1 gclusters)
    fun node_no_next2 parent_top_meta_vars gcluster = ZN.node_no_next2 exn
      (Node.co2 parent_top_meta_vars gcluster)
  in
  fun run_monad {ctxt : Proof.context(*, state : @{ParaT_arg 0}*)} :
    (@{ParaT_args} 'a) M.t -> {ctxt : Proof.context(*, state : @{ParaT_arg 0}*), result : 'a} option =
    (*State_MSTrans.run state #>*) Ctxt_MSTrans.run ctxt #> Option.map (fn x =>
      let
        val ctxt = Ctxt_MSTrans.SR.state x
        (* val x = Ctxt_MSTrans.SR.value x
        val state = State_MSTrans.SR.state x
        val result = State_MSTrans.SR.value x *)
        val result = Ctxt_MSTrans.SR.value x
      in {ctxt = ctxt(*, state = state*), result = result} end)
  fun init_thm_state (st : Zippy_Thm_State.state) : (@{ParaT_args} @{AllT_args} Z1.zipper) M.t =
    LGoals.init_state
      (node_no_next1 #> ZN.container_no_parent exn #> Container.init_container1 #> Z1.ZM.Zip.morph)
      (node_no_next2 (Zippy_Thm_State.meta_vars st)) st
  end
end
end
end
\<close>

ML\<open>
(*add runs*)
structure Zippy =
struct open Zippy
structure Run =
struct
fun with_state f = Ctxt.with_ctxt (fn ctxt => (*State.with_state (fn state =>*)
  f {ctxt = ctxt(*, state = state*)})
local
  structure Base_Mixins =
  struct
    structure Z = ZLPC
    structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} = Show.Zipper{i}
    structure Show_Container{i} = Show.Container{i}\<close>\<close>
  end
  structure ZE = Zippy_Enum_Mixin(open Base_Mixins; open Z)
  structure Goals_Results = Zippy_Goals_Results_Mixin_Base(open LGoals_Pos_Copy
    structure GClusters_Results = Mixin_Base1.Results; structure GCluster_Results = Mixin_Base2.Results)
  structure Goals_Results_TMV = Zippy_Goals_Results_Top_Meta_Vars_Mixin_Base(open Goals_Results
    structure Top_Meta_Vars = Mixin_Base2.Top_Meta_Vars)
  structure CAction = Zippy_CAction_Mixin(open Base_Mixins
    structure CAction = Mixin_Base4.CAction; structure Log = Logging.CAction; structure Show = Show4)
  structure Run = Zippy_Run_Mixin(open Base_Mixins
    structure Run = Zippy_Run_Mixin_Base(open Goals_Results
      structure Seq_From_Monad = Seq_From_Monad)
    val with_state = with_state
    structure Log = Zippy_Logger_Mixin_Base(val parent_logger = Logging.logger; val name =  "Run"))
  val mk_exn = Library.K Util.exn
in
open Run
val with_state = with_state
local open MU; open SC A Mo
  structure GClusters = Zippy_Goal_Clusters_Mixin(GClusters)
  structure GClusters_Results = Zippy_Goal_Results_Mixin(GClusters_Results)
  structure LGoals_Results_TMV = Zippy_Lists_Goals_Results_Top_Meta_Vars_Mixin(open Base_Mixins
    structure Z = Zippy_Lists(open Base_Mixins)
    structure Goals_Results_Top_Meta_Vars = Goals_Results_TMV; structure Log_LGoals = Logging.LGoals)
  structure EAction_App_Meta = Zippy_Enum_Action_App_Metadata_Mixin(
    structure Z = ZE
    structure Meta = Zippy_Action_App_Metadata_Mixin(Zippy.Mixin_Base5.Meta))
in
fun run_statesq init_sstate step finish fuel c = init_sstate c
  >>= with_state (fn ms => arr (fn ss =>
    repeat_step step finish finish fuel ss ms c))
  >>= arr (Seq.maps (Zippy_Run_Result.cases #thm_states I))
fun run_statesq' init_sstate step mk_unreturned_statesq = run_statesq init_sstate step (fn _ => fn _ =>
  ZLPC.Z1.ZM.Zip.morph >>> mk_unreturned_statesq >>> arr (Zippy_Run_Result.Unfinished #> Seq.single))
fun mk_df_post_unreturned_statesq x = mk_unreturned_statesq (Ctxt.with_ctxt
  (LGoals_Results_TMV.mk_statesq (LGoals_Results_TMV.enum_df_post_children2 mk_exn))) x
fun mk_df_post_unreturned_promising_statesq x = mk_unreturned_statesq (Ctxt.with_ctxt
  (LGoals_Results_TMV.mk_statesq (EAction_App_Meta.enum_df_post_promising_children2 mk_exn))) x
end
structure Best_First =
struct
  structure Logging =
  struct
    val logger = Logger.setup_new_logger logger "Best_First"
    local structure Base = struct val parent_logger = logger end
    in
    structure CAction_Queue = Zippy_Logger_Mixin_Base(open Base; val name = "CAction_Queue")
    structure Step = Zippy_Logger_Mixin_Base(open Base; val name = "Step")
    end
  end
  local open MU.Mo
    structure ZCost = Zippy_Collect_Trace_Mixin(ZLPC.ZCollect)
  in
  fun mk_prio {cost, zipper,...} = ZCost.ZZCollect_Co4.getter zipper |> ZCost.get_current
    |> Option.map (Library.curry Cost.add cost) |> the_default cost |> pure
  structure CAction_Queue = Zippy_CAction_Queue_Mixin(open Base_Mixins
    structure Z = ZE
    structure CAction_Queue = Zippy_CAction_Queue_Mixin_Base(structure CAction = CAction
      structure Queue = Leftist_Heap(type prio = Cost.cost; val ord = Cost.ord))
    val mk_prio = mk_prio
    val mk_exn = mk_exn
    structure Log = Logging.CAction_Queue)
  end
  structure Show_Queue_Entry = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} CAction_Queue.entry
    fun pretty ctxt {cost, zipper,...} = SpecCheck_Show.record [
      ("Cost", Show.Cost.pretty ctxt cost),
      ("Zipper", Show.Zipper4.pretty ctxt zipper)])
  structure Step = Zippy_Step_Mixin(open Base_Mixins
    structure Step = Zippy_Step_Mixin_Base(open Goals_Results_TMV
      structure CAction_Queue = CAction_Queue)
    val mk_prio = mk_prio
    val mk_exn = mk_exn
    structure Log = Logging
    structure Log_LGoals = Zippy.Logging.LGoals
    structure Log_CAction_Queue = Logging.CAction_Queue
    structure Show_Queue_Entry = Show_Queue_Entry
    structure Show_Prio = Show.Cost)
  end
end
end
end
\<close>

end
