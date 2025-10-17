\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Pure
  imports
    Zippy_Instance
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

(* instance and utilities *)
  val exn : @{ParaT_args encl: "(" ")"} ME.exn = ()
  structure Zippy_Base = Zippy_Instance_Base(structure ME = ME; type prio = Prio.prio)
  structure Logging =
  struct
    val logger = Logger.setup_new_logger zippy_base_logger "Zippy"
    local structure Base = struct val parent_logger = logger end
    in
    structure Copy = Zippy_Logger_Mixin_Base(open Base; val name = "Copy")
    structure Enum_Copy = Zippy_Logger_Mixin_Base(open Base; val name = "Enum_Copy")
    structure PAction = Zippy_Logger_Mixin_Base(open Base; val name = "PAction")
    structure LGoals = Zippy_Logger_Mixin_Base(open Base; val name = "LGoals")
    structure LGoals_Pos_Copy = Zippy_Logger_Mixin_Base(open Base; val name = "LGoals_Pos_Copy")
    structure PAction_PResults = Zippy_Logger_Mixin_Base(open Base; val name = "PAction_PResults")
    structure Result_Action = Zippy_Logger_Mixin_Base(open Base; val name = "Result_Action")
    end
  end
  structure Zippy = Zippy_Instance(
    structure Z = Zippy_Base; structure Ctxt = Ctxt structure Log_LGoals = Logging.LGoals
    structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy
    structure Show_Prio = Zippy_Show_Mixin_Base(
      type @{AllT_args} t = Prio.prio
      val pretty = Library.K Prio.pretty))
  structure Zippy_PAction = Zippy_Instance_PAction(
    structure Z = Zippy
    val mk_exn = Library.K exn
    structure Ctxt = Ctxt; structure Log_Result_Action = Logging.Result_Action;
    structure Log_LGoals = Logging.LGoals structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy;
    structure Log_Copy = Logging.Copy structure Log_Enum_Copy = Logging.Enum_Copy)
  structure Zippy_PResults = Zippy_Instance_PResults(
    structure Z = Zippy_PAction
    val halve = Prio.halve
    structure Ctxt = Ctxt; structure Log_PAction = Logging.PAction
    structure Log_PAction_PResults = Logging.PAction_PResults)
  structure Zippy_Tactic = Zippy_Instance_Tactic(
    structure Z = Zippy_PResults; structure Ctxt = Ctxt; structure Log_PAction = Logging.PAction)
in
(* final creation of structure *)
structure Zippy =
struct
open Zippy_Base Zippy Zippy_PAction Zippy_PResults Zippy_Tactic
(** add loggers **)
structure Logging = Logging
(** add monads and priority **)
(* structure State_MSTrans = MS
structure State = Zippy_State_Mixin(Zippy_State_Mixin_Base(MS)) *)
structure Ctxt_MSTrans = Ctxt_MSTrans
structure Ctxt = Ctxt
structure Prio = Prio
(** add compound mixins **)
local
  structure Base_Mixins = struct structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt end
  structure ZL = Zippy_Lists(open Base_Mixins; structure Z = ZLP)
  structure Goals = Zippy_Goals_Mixin_Base(
    structure GClusters = Mixin1.GClusters; structure GCluster = Mixin2.GCluster)
  structure Goals_Pos = Zippy_Goals_Pos_Mixin(structure Z = ZLP
    structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU))
  structure Goals_Pos_Copy = Zippy_Goals_Pos_Copy_Mixin(Zippy_Goals_Pos_Copy_Mixin_Base(open Goals_Pos
    structure Copy = Mixin3.Copy))
in
structure LGoals_Pos_Copy = Zippy_Lists_Goals_Pos_Copy_Mixin(open Base_Mixins; structure Z = ZL
  structure GPC = Goals_Pos_Copy;
  structure Log = Logging.LGoals_Pos_Copy; structure Log_LGoals = Logging.LGoals
  structure Show1 = Show.Zipper1; structure Show2 = Show.Zipper2; structure Show3 = Show.Zipper3)
end
(** add instance specific utilities **)
structure Util =
struct
  val exn = exn
  local
    open ZLP
    structure ZN = Zippy_Node(structure Z = ZLP; structure Exn = Exn)
    structure ZL = Zippy_Lists(structure Z = ZLP; structure Co = Co)
    structure Goals = Zippy_Goals_Mixin_Base(
      structure GClusters = Mixin1.GClusters; structure GCluster = Mixin2.GCluster)
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
  fun init_thm_state (state : Zippy_Thm_State.state) : (@{ParaT_args} @{AllT_args} Z1.zipper) M.t =
    LGoals.init_state
      (node_no_next1 #> ZN.container_no_parent exn #> Container.init_container1 #> Z1.ZM.Zip.morph)
      (node_no_next2 (Zippy_Thm_State.meta_vars state)) state
  end
end
end
end
\<close>

ML\<open>
(*add best-first-search*)
structure Zippy =
struct open Zippy
local
  structure Base_Mixins =
  struct
    structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} = Show.Zipper{i}
    structure Show_Container{i} = Show.Container{i}\<close>\<close>
  end
  structure Goals_Results = Zippy_Goals_Results_Mixin_Base(open LGoals_Pos_Copy
    structure GClusters_Results = Mixin1.Results; structure GCluster_Results = Mixin2.Results)
  structure Goals_Results_TMV = Zippy_Goals_Results_Top_Meta_Vars_Mixin_Base(open Goals_Results
    structure Top_Meta_Vars = Mixin2.Top_Meta_Vars)
  structure PAction = Zippy_PAction_Mixin(open Base_Mixins
    structure PAction = Mixin4.PAction; structure Log = Logging.PAction; structure Show = Show4)
  structure Logging =
  struct
    local structure Base = struct val parent_logger = Logging.logger end
    in
    structure PAction_Queue = Zippy_Logger_Mixin_Base(open Base; val name = "PAction_Queue")
    structure Step = Zippy_Logger_Mixin_Base(open Base; val name = "Step")
    structure Run = Zippy_Logger_Mixin_Base(open Base; val name = "Run")
    end
  end
  structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(
    structure PAction = PAction
    structure Queue = Leftist_Heap(type prio = Prio.prio; val ord = Prio.ord #> rev_order))
  structure Show_Queue_Entry = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} PAction_Queue.entry
    fun pretty ctxt {prio, zipper,...} = SpecCheck_Show.record [
      ("Priority", Show.Prio.pretty ctxt prio),
      ("Zipper", Show.Zipper4.pretty ctxt zipper)
    ])
  structure Step = Zippy_Step_Mixin_Base(open Goals_Results_TMV
    structure PAction_Queue = PAction_Queue)
  structure Run = Zippy_Run_Mixin(open Base_Mixins
    structure Z = ZLP
    structure Run = Zippy_Run_Mixin_Base(
      structure Step = Step; structure Action_App_Meta = Mixin5.Meta)
    type @{AllT_args} state = {ctxt : Proof.context(*, state : @{ParaT_arg 0}*)}
    fun seq_from_monad {ctxt(*, state*)} =
      (*State_MSTrans.eval state #>*) Ctxt_MSTrans.eval ctxt #> the_default Seq.empty
    fun with_state f = Ctxt.with_ctxt (fn ctxt => (*State.with_state (fn state =>*)
      f {ctxt = ctxt(*, state = state*)})
    val mk_exn = Library.K Util.exn
    structure Log = Logging.Run; structure Log_LGoals = Zippy.Logging.LGoals
    structure Log_PAction_Queue = Logging.PAction_Queue; structure Log_Step = Logging.Step
    structure Show_Queue_Entry = Show_Queue_Entry)
in
structure Run_Best_First =
struct
  structure Logging = Logging
  structure Show_Queue_Entry = Show_Queue_Entry
  open Run
end
end
end
\<close>

end
