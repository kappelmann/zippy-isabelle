(*  Title:      Zippy/zippy_instance.ML
    Author:     Kevin Kappelmann
*)
@{record (sig) NODE_CO_BASE1 [gclusters, results]}
@{record (sig) NODE_CO_BASE2 [gcluster, results, top_meta_vars]}
@{record (sig) NODE_CO_BASE3 [copy, meta]}
@{record (sig) NODE_CO_BASE4 [paction, presults, action_app_num, focus, meta]}
@{record (sig) NODE_CO_BASE5 [action_app_num, focus, prio, result_meta]}

functor Zippy_Instance(
    type prio
    val prio_ord : prio ord
  ) =
struct

(* monads and arrows *)
structure ME = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))
structure MS = \<^eval>\<open>sfx_ParaT_nargs "IState_Trans"\<close>(
  structure M = ME; structure SR = Pair_State_Result_Base)
structure ME = \<^eval>\<open>sfx_ParaT_nargs "IMonad_Exception_State_Trans"\<close>(
  structure M = ME; structure S = MS)
structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close> =
struct open ME; type (@{ParaT_args} 'a) t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) t end
structure MU = Zippy_Monad_Util(ME)
structure MEU = Zippy_Monad_Exception_Util(ME)

(* misc *)
structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
  structure AE = MEU.AE; structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(MEU.A))

structure Tac = Standard_Zippy_ZTactic

val exn : @{ParaT_args encl = "(" ")"} MEU.AE.exn = ()

(* construction *)

local
  (** node content base data **)
  @{record (struct) Node_Co_Base1 NODE_CO_BASE1 [gclusters, results]}
  @{record (struct) Node_Co_Base2 NODE_CO_BASE2 [gcluster, results, top_meta_vars]}
  @{record (struct) Node_Co_Base3 NODE_CO_BASE3 [copy, meta]}
  @{record (struct) Node_Co_Base4 NODE_CO_BASE4 [paction, presults, action_app_num, focus, meta]}
  @{record (struct) Node_Co_Base5 NODE_CO_BASE5 [action_app_num, focus, prio, result_meta]}

  (** alternating zipper skeleton **)
  structure ZLP = Zippy_Lists_Positions_Mixin_Base(
    structure ME = ME; structure Z = Zippy_Lists_Base(ME))

  (** add data **)
  structure GCS = Standard_Zippy_Goal_Clusters
  structure GC = Standard_Zippy_Goal_Cluster
  structure Top_Meta_Vars = Zippy_Top_Meta_Vars
  structure GResults = Zippy_Goal_Results
  type copy_update_data = Tac.GPU.focus_update
  structure ACMeta = Zippy_Action_Cluster_Metadata
  structure TRMeta = Zippy_Tactic_Result_Metadata
  type result = TRMeta.metadata Tac.result
  structure AResult = Zippy_Action_Result
  structure AAN = Zippy_Action_App_Num
  structure AMeta = Zippy_Action_Metadata
  structure GF = Standard_Zippy_Goal_Focus

  (*** create recursive datatypes ***)
  local structure Z : ZIPPY_BASE_BASE = ZLP; open Z
  in
  datatype @{AllT_args} copy = Copy of copy_update_data -> @{AllT_args} zipper3 ->
    (@{ParaT_args} @{AllT_args} zipper1) hom_move
  and @{AllT_args} paction = PAction of (@{ParaT_args} @{AllT_args} zipper4, prio *
    (prio -> (@{ParaT_args} @{AllT_args} zipper4,
      (@{AllT_args} zipper4, @{AllT_args} zipper5, @{AllT_args} zipper1) AResult.result) move)) cat
  and @{AllT_args} presults = PResults of
    (@{ParaT_args} @{AllT_args} zipper4, prio, result) Co.acoroutine
  withtype
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  @{AllT_args} zipper{i} = (@{ParaT_args}
      (GCS.gclusters, GResults.results) Node_Co_Base1.data,

      (GC.gcluster, GResults.results, Top_Meta_Vars.top_meta_vars) Node_Co_Base2.data,

      (@{AllT_args} copy, ACMeta.metadata) Node_Co_Base3.data,

      (@{AllT_args} paction, @{AllT_args} presults, AAN.action_app_num, GF.focus, AMeta.metadata)
        Node_Co_Base4.data,

      (AAN.action_app_num, GF.focus, prio, TRMeta.metadata) Node_Co_Base5.data
    ) Z{i}.zipper
  \<close> where sep = "and"\<close>
  end
  type @{AllT_args} inst1 = (GCS.gclusters, GResults.results) Node_Co_Base1.data
  type @{AllT_args} inst2 = (GC.gcluster, GResults.results,
    Top_Meta_Vars.top_meta_vars) Node_Co_Base2.data
  type @{AllT_args} inst3 = (@{AllT_args} copy, ACMeta.metadata) Node_Co_Base3.data
  type @{AllT_args} inst4 = (@{AllT_args} paction, @{AllT_args} presults, AAN.action_app_num,
    GF.focus, AMeta.metadata) Node_Co_Base4.data
  type @{AllT_args} inst5 = (AAN.action_app_num, GF.focus, prio, TRMeta.metadata) Node_Co_Base5.data
in

(*** instantiate data in alternating zipper skeleton ***)
local open ZLP.ZP
in
structure ZP :
  ZIPPY_POSITIONS_MIXIN_BASE
  where type @{AllT_args} ZLPos.Z.ZM.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZLPos.Z.ZM.zipper
  where type @{AllT_args} ZLPos.Z.ZD.zcontext = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZLPos.Z.ZD.zcontext
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZLPos.Z{i}.ZM.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZLPos.Z{i}.ZM.zipper
  where type @{AllT_args} ZLPos.Z{i}.ZD.content = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZLPos.Z{i}.ZD.content
  where type @{AllT_args} ZLPos.Z{i}.ZD.zcontext = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZLPos.Z{i}.ZD.zcontext
  where type @{AllT_args} ZLPos.pzipper{i} = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZLPos.pzipper{i}
  where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.ZM.container
  where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.ZD.zcontext
  where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.zipper\<close>\<close>
  = ZLP.ZP
end
local open ZLP
in
structure ZL :
  ZIPPY_LISTS_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZN_AZ{i}.ZM.container = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN_AZ{i}.ZM.container
  where type @{AllT_args} ZN_AZ{i}.ZD.content = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN_AZ{i}.ZD.content\<close>
  where stop = 1\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZN_AZ{i}.ZD.content = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN_AZ{i}.ZD.content
  where type @{AllT_args} ZN_AZ{i}.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN_AZ{i}.zipper\<close>
  where start = 2\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZN.A.Z{i}.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN.A.Z{i}.zipper
  where type @{AllT_args} ZN.A.N{i}.content = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN.A.N{i}.content
  where type @{AllT_args} ZN.Z{i}.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN.Z{i}.zipper
  where type @{AllT_args} ZN.zcontext{i} = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN.zcontext{i}
  where type @{AllT_args} ZN.pzipper{i} = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) ZN.pzipper{i}
  where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.ZM.container
  where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.ZD.zcontext
  where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
    \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z{i}.zipper\<close>\<close>
  = ZLP
end

(*** instantiated alternating zippers ***)
structure ZP = Zippy_Positions_Mixin(structure Z = ZP; structure AE = MEU.AE)
structure ZL = Zippy_Lists(structure Z = ZL; structure Co = Co)
structure ZN = Zippy_Node(structure Z = ZL; structure AE = MEU.AE)
structure ZB = Zippy_Base(structure Z = ZL; structure AE = MEU.AE)
structure ZE = Zippy_Base_Enum(structure Z = ZL; structure Co = Co)
structure ZS = Zippy_State_Mixin(open ZL; structure MS = MS)
local structure Z : ZIPPY_BASE_BASE = ZB in open Z end
\<^imap>\<open>\<open>{i}\<close> => \<open>
val container{i} : @{AllT_args} ZP.ZGPos.Z{i}.ZM.container ->
  @{AllT_args} ZP.ZLPos.Z{i}.ZM.container ->
  @{AllT_args} ZP.ZDepth.Z{i}.ZM.container ->
  @{AllT_args} ZN.ZN.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container =
  ZLP.container{i}
val init_container{i} : @{AllT_args} ZN.ZN.Z{i}.ZM.container ->
  @{AllT_args} Z{i}.ZM.container =
  ZLP.init_container{i}\<close>\<close>

local structure Base =
  struct
    structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>; open L
    fun gen_mk_lens l getter modifier = L.comp (L.mk_lens getter (uncurry modifier)) (l ())
  end
in
(*** goal clusters ***)
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base1
    type @{AllT_args} container = @{AllT_args} Z1.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co1.lens x
  end
in
structure NCo1 =
struct
  structure CB = Base.NCB
  structure GClusters = Zippy_Goal_Clusters_Mixin(Zippy_Goal_Clusters_Mixin_Base(
    structure GCS = GCS
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = GCS.gclusters
      fun lens _ = mk_lens NCB.get_gclusters NCB.map_gclusters)))
  structure Results = Zippy_Goal_Results_Mixin(Zippy_Goal_Results_Mixin_Base(
    structure R = GResults
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = GResults.results
      fun lens _ = mk_lens NCB.get_results NCB.map_results)))
end
end

(*** goal cluster ***)
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base2
    type @{AllT_args} container = @{AllT_args} Z2.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co2.lens x
  end
in
structure NCo2 =
struct
  structure CB = Base.NCB
  structure GCluster = Zippy_Goal_Cluster_Mixin(Zippy_Goal_Cluster_Mixin_Base(
    structure GC = GC
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = GC.gcluster
      fun lens _ = mk_lens NCB.get_gcluster NCB.map_gcluster)))
  structure Results = Zippy_Goal_Results_Mixin(Zippy_Goal_Results_Mixin_Base(
    structure R = GResults
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = GResults.results
      fun lens _ = mk_lens NCB.get_results NCB.map_results)))
  structure Top_Meta_Vars = Zippy_Top_Meta_Vars_Mixin(Zippy_Top_Meta_Vars_Mixin_Base(
    structure TMV = Top_Meta_Vars
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = Top_Meta_Vars.top_meta_vars
      fun lens _ = mk_lens NCB.get_top_meta_vars NCB.map_top_meta_vars)))
  structure Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin(
    structure Z = ZL
    structure Goal_Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin_Base(
      structure Top_Meta_Vars = Top_Meta_Vars; structure Results = Results))
end
end

structure Goals = Zippy_Goals_Mixin_Base(
  structure GClusters = NCo1.GClusters; structure GCluster = NCo2.GCluster)
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = ZL; structure Goals = Goals)
structure Goals_Results = Zippy_Goals_Results_Mixin_Base(open Goals
  structure GClusters_Results = NCo1.Results
  structure GCluster_Results = NCo2.Results)
structure LGoals_Results = Zippy_Lists_Goals_Results_Mixin(
  structure Z = ZL; structure Goals_Results = Goals_Results)

(*** action clusters ***)
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base3
    type @{AllT_args} container = @{AllT_args} Z3.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co3.lens x
  end
in
structure NCo3 =
struct
  structure CB = Base.NCB
  structure Copy = Zippy_Copy_Mixin(
    structure Copy = Zippy_Copy_Mixin_Base(
      structure M = ZB
      structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
        type @{AllT_args} data = @{AllT_args} copy
        fun lens _ = mk_lens NCB.get_copy NCB.map_copy)
      type @{AllT_args} zipper_to = @{AllT_args} Z1.zipper
      type copy_update_data = copy_update_data
      val copy = Copy
      fun run_copy (Copy copy) = copy)
    structure AE = MEU.AE)
  structure ECopy = Zippy_Enum_Copy_Mixin(structure Z = ZE; structure Copy = Copy)
  structure Meta = Zippy_Action_Cluster_Metadata_Mixin_Base(
    structure Meta = ACMeta
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = Meta.metadata
      fun lens _ = mk_lens NCB.get_meta NCB.map_meta))
end
end

(*** actions ***)
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base4
    type @{AllT_args} container = @{AllT_args} Z4.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co4.lens x
  end
in
structure NCo4 =
struct
  structure CB = Base.NCB
  structure PAction = Zippy_PAction_Mixin(
    structure PAction = Zippy_PAction_Mixin_Base(
      structure M = ZB
      structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
        type @{AllT_args} data = @{AllT_args} paction
        fun lens _ = mk_lens NCB.get_paction NCB.map_paction)
      structure AResult = AResult
      type @{AllT_args} zipper_expand = @{AllT_args} Z5.zipper
      type @{AllT_args} zipper_trim = @{AllT_args} Z1.zipper
      type prio = prio
      val paction = PAction
      fun run_paction (PAction paction) = paction)
    structure AE = MEU.AE)

  structure PResults = Zippy_PResults_Mixin(Zippy_PResults_Mixin_Base(
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = @{AllT_args} presults
      fun lens _ = mk_lens NCB.get_presults NCB.map_presults)
    structure K = ZB.K
    structure Co = ZL.Co
    type prio = PAction.prio
    type result = result
    val presults = PResults
    fun dest_presults (PResults presults) = presults))

  structure PResults_Pos = Zippy_PResults_Positions_Mixin(
    structure Z = ZP; structure PResults = PResults)

  structure PAction_PResults = Zippy_PAction_PResults_Mixin(Zippy_PAction_PResults_Mixin_Base(
    structure PResults = PResults; structure PAction = PAction))

  structure ActionAN = Zippy_Action_App_Num_Mixin(Zippy_Action_App_Num_Mixin_Base(
    structure AAN = AAN
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = AAN.action_app_num
      fun lens _ = mk_lens NCB.get_action_app_num NCB.map_action_app_num)))

  structure Goal_Focus = Zippy_Goal_Focus_Mixin_Base(
    structure F = GF
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = GF.focus
      fun lens _ = mk_lens NCB.get_focus NCB.map_focus))

  structure Meta = Zippy_Action_Cluster_Metadata_Mixin_Base(
    structure Meta = AMeta
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = Meta.metadata
      fun lens _ = mk_lens NCB.get_meta NCB.map_meta))
end
end

structure PAction_Queue = Zippy_PAction_Queue_Mixin(
  structure Z = ZE
  structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(
    structure PAction = NCo4.PAction
    structure Queue = Leftist_Heap(type prio = prio; val ord = (prio_ord #> rev_order)))
  val mk_exn = Library.K exn)

(*** action applications ***)
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base5
    type @{AllT_args} container = @{AllT_args} Z5.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co5.lens x
  end
in
structure NCo5 =
struct
  structure CB = Base.NCB
  structure ActionAN = Zippy_Action_App_Num_Mixin(Zippy_Action_App_Num_Mixin_Base(
    structure AAN = AAN
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = AAN.action_app_num
      fun lens _ = mk_lens NCB.get_action_app_num NCB.map_action_app_num)))

  structure Goal_Focus = Zippy_Goal_Focus_Mixin_Base(
    structure F = GF
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = GF.focus
      fun lens _ = mk_lens NCB.get_focus NCB.map_focus))

  structure Prio = Zippy_Prio_Mixin_Base(
    type prio = NCo4.PAction.prio
    structure L =
      \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
        type @{AllT_args} data = prio
        fun lens _ = mk_lens NCB.get_prio NCB.map_prio))

  structure Result_Meta = Zippy_Tactic_Result_Metadata_Mixin(Zippy_Tactic_Result_Metadata_Mixin_Base(
    structure Meta = TRMeta
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = Meta.metadata
      fun lens _ = mk_lens NCB.get_result_meta NCB.map_result_meta)))
end
end
end
end

(* tactics *)
structure Goals_Tac = Zippy_Goals_Tactic_Mixin_Base(open Goals; structure Tac = Tac)
structure LGoals_Tac = Zippy_Lists_Goals_Tactic_Mixin(
  structure Z = ZL; structure Goals_Tac = Goals_Tac)

structure GTC = Zippy_Goals_Tactic_Copy_Mixin(
  Zippy_Goals_Tactic_Copy_Mixin_Base(open Goals_Tac; structure Copy = NCo3.Copy))
structure LGTC = Zippy_Lists_Goals_Tactic_Copy_Mixin(
  structure Z = ZL; structure GTC = GTC)

structure GTCP = Zippy_Goals_Tactic_Copy_PAction_Mixin_Base(
  open GTC; structure PAction = NCo4.PAction)
structure LGTCP = Zippy_Lists_Goals_Tactic_Copy_PAction_Mixin(
  structure Z = ZL; structure GTCP = GTCP)

(* runs *)
structure Runs = Zippy_Runs_Mixin(
  structure Z = struct open ZL; structure ZP = ZP end
  structure Co = Co
  structure Runs = Zippy_Runs_Mixin_Base(open Goals_Results
    structure Top_Meta_Vars = NCo2.Top_Meta_Vars; structure PAction_Queue = PAction_Queue)
  val mk_exn = Library.K exn)
structure SRuns = Zippy_State_Runs_Mixin(
  structure Z = struct open ZL; structure ZP = ZP; structure ZS = ZS end
  structure Co = Co
  structure Runs = Runs
  val mk_exn = Library.K exn
  fun seq_from_monad x = the_default Seq.empty x)

(* pretty printing *)
local structure Show = SpecCheck_Show_Base
in
structure NCo1 =
struct
  open NCo1
  fun pretty ctxt n = Show.record [
    ("Goal clusters", GClusters.GCS.pretty_gclusters ctxt (GClusters.L.getter n)),
    ("Results", Results.R.pretty_results (Results.L.getter n))
  ]
end
structure NCo2 =
struct
  open NCo2
  fun pretty ctxt n = Show.record [
    ("Goal cluster", GCluster.GC.pretty_gcluster ctxt (GCluster.L.getter n)),
    ("Results", Results.R.pretty_results (Results.L.getter n)),
    ("Top Meta Variables", Top_Meta_Vars.TMV.pretty ctxt (Top_Meta_Vars.L.getter n))
  ]
end
structure NCo3 =
struct
  open NCo3
  fun pretty n = Show.record [
    ("Metadata", Meta.Meta.pretty_metadata (Meta.L.getter n))
  ]
end
structure NCo4 =
struct
  open NCo4
  fun pretty n = Show.record [
    ("Action application number", ActionAN.AAN.pretty (ActionAN.L.getter n)),
    ("Focus", Goal_Focus.F.pretty (Goal_Focus.L.getter n)),
    ("Metadata", Meta.Meta.pretty_metadata (Meta.L.getter n))
  ]
end
structure NCo5 =
struct
  open NCo5
  fun pretty (pretty_prio : prio Show.show) n = Show.record [
    ("Action application number", ActionAN.AAN.pretty (ActionAN.L.getter n)),
    ("Focus", Goal_Focus.F.pretty (Goal_Focus.L.getter n)),
    ("Priority", pretty_prio (Prio.L.getter n)),
    ("Result Metadata", Result_Meta.Meta.pretty_metadata (Result_Meta.L.getter n))
  ]
end
end

end