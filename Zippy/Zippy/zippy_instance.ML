(*  Title:      Zippy/zippy_instance.ML
    Author:     Kevin Kappelmann
*)
@{record (sig) NODE_CO_BASE1 [gclusters, results]}
@{record (sig) NODE_CO_BASE2 [gcluster, results, top_meta_vars]}
@{record (sig) NODE_CO_BASE3 [copy, meta]}
@{record (sig) NODE_CO_BASE4 [paction, presults, action_app_num, focus, meta]}
@{record (sig) NODE_CO_BASE5 [action_app_num, focus, prio, result_meta]}

functor Zippy_Instance(
    structure FIA : FUNCTOR_INSTANCE_ARGS
    type prio
    val prio_ord : prio ord
    val pretty_prio : prio -> Pretty.T
  ) =
struct

local structure FIU = Functor_Instance_Util(FIA)
in
val logger = Logger.setup_new_logger zippy_logger FIU.base_name
end

(* monads, arrows, and basic mixins *)
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

  (** arbitrary state **)
  structure MS = \<^eval>\<open>sfx_ParaT_nargs "IState_Trans"\<close>(
    structure M = Ctxt_MSTrans; structure SR = Pair_State_Result_Base)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "IMonad_Exception_State_Trans"\<close>(
    structure M = ME; structure S = MS)
  structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close> =
  struct open ME; type (@{ParaT_args} 'a) t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) t end
  structure MCtxt = \<^eval>\<open>sfx_ParaT_nargs "IMonad_State_State_Trans"\<close>(
    type ParaT = unit; structure M = Ctxt_MSTrans; structure S = MS)
in
structure State_MSTrans = MS
structure State = Zippy_State_Mixin(Zippy_State_Mixin_Base(MS))
structure Exn = Zippy_Exception_Mixin(Zippy_Exception_Mixin_Base(ME))
structure Ctxt_MSTrans = Ctxt_MSTrans
structure Ctxt = Zippy_Ctxt_State_Mixin(Zippy_Ctxt_State_Mixin_Base(MCtxt))
structure Co = Zippy_Coroutine_Mixin_Base(open Exn
  structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
    structure AE = AE; structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(AE)))
structure MU = Zippy_Monad_Util(ME)
end

(* misc *)
structure Tac = Standard_Zippy_ZTactic
val exn : @{ParaT_args encl = "(" ")"} Exn.ME.exn = ()

(* construction of alternating zipper *)
local
  (** node content base data **)
  @{record (struct) Node_Co_Base1 NODE_CO_BASE1 [gclusters, results]}
  @{record (struct) Node_Co_Base2 NODE_CO_BASE2 [gcluster, results, top_meta_vars]}
  @{record (struct) Node_Co_Base3 NODE_CO_BASE3 [copy, meta]}
  @{record (struct) Node_Co_Base4 NODE_CO_BASE4 [paction, presults, action_app_num, focus, meta]}
  @{record (struct) Node_Co_Base5 NODE_CO_BASE5 [action_app_num, focus, prio, result_meta]}

  (** alternating zipper skeleton **)
  structure ZLP = Zippy_Lists_Positions_Mixin_Base(
    structure Exn = Exn; structure Z = Zippy_Lists_Base(Exn))

  (** add data **)
  structure GCS = Standard_Zippy_Goal_Clusters
  structure GC = Standard_Zippy_Goal_Cluster
  structure Top_Meta_Vars = Zippy_Top_Meta_Vars
  structure GResults = Zippy_Goal_Results
  type copy_update_data = Tac.GPU.focus_update
  structure ACMeta = Zippy_Action_Cluster_Metadata
  structure AResult = Zippy_Action_Result
  structure AMeta = Zippy_Action_Metadata
  structure AANum = Zippy_Action_App_Num
  structure AAMeta = Zippy_Action_App_Metadata
  type result = AAMeta.metadata Tac.result
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
    (@{ParaT_args} @{AllT_args} zipper4, prio, result) Co.Co.acoroutine
  withtype
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  @{AllT_args} zipper{i} = (@{ParaT_args}
      (GCS.gclusters, GResults.results) Node_Co_Base1.data,

      (GC.gcluster, GResults.results, Top_Meta_Vars.top_meta_vars) Node_Co_Base2.data,

      (@{AllT_args} copy, ACMeta.metadata) Node_Co_Base3.data,

      (@{AllT_args} paction, @{AllT_args} presults, AANum.action_app_num, GF.focus, AMeta.metadata)
        Node_Co_Base4.data,

      (AANum.action_app_num, GF.focus, prio, AAMeta.metadata) Node_Co_Base5.data
    ) Z{i}.zipper
  \<close> where sep = "and"\<close>
  end
  type @{AllT_args} inst1 = (GCS.gclusters, GResults.results) Node_Co_Base1.data
  type @{AllT_args} inst2 = (GC.gcluster, GResults.results,
    Top_Meta_Vars.top_meta_vars) Node_Co_Base2.data
  type @{AllT_args} inst3 = (@{AllT_args} copy, ACMeta.metadata) Node_Co_Base3.data
  type @{AllT_args} inst4 = (@{AllT_args} paction, @{AllT_args} presults, AANum.action_app_num,
    GF.focus, AMeta.metadata) Node_Co_Base4.data
  type @{AllT_args} inst5 = (AANum.action_app_num, GF.focus, prio, AAMeta.metadata) Node_Co_Base5.data
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

(* basic mixins and functions for alternating zipper *)
structure ZP = Zippy_Positions_Mixin(structure Z = ZP; structure Exn = Exn)
structure ZL = Zippy_Lists(structure Z = ZL; structure Co = Co)
structure ZB = Zippy_Base(structure Z = ZL; structure Exn = Exn)
structure ZE = Zippy_Enum_Mixin(Zippy_Enum_Mixin_Base(structure Z = ZL; structure Co = Co))
structure ZN = Zippy_Node(structure Z = ZL; structure Exn = Exn)
local structure Z : ZIPPY_BASE_BASE = ZB in open Z end

(** container constructors **)
\<^imap>\<open>\<open>{i}\<close> => \<open>
val container{i} : @{AllT_args} ZP.ZGPos.Z{i}.ZM.container ->
  @{AllT_args} ZP.ZLPos.Z{i}.ZM.container -> @{AllT_args} ZP.ZDepth.Z{i}.ZM.container ->
  @{AllT_args} ZN.ZN.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container =
  ZLP.container{i}
val init_container{i} : @{AllT_args} ZN.ZN.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container =
  ZLP.init_container{i}\<close>\<close>

structure ZLP = Zippy_Lists_Positions_Mixin(
  structure Z = struct open ZL; structure ZP = ZP end; structure Exn = Exn)

(* lenses *)
local
  structure Base =
  struct
    structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
    fun gen_mk_lens l getter modifier = L.comp (L.mk_lens getter (uncurry modifier)) (l ())
  end
in
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base1
    type @{AllT_args} container = @{AllT_args} Z1.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co1.lens x
  end
in
structure Lens1 =
struct
  structure NCB = Base.NCB
  structure GClusters = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GCS.gclusters
    fun lens _ = mk_lens NCB.get_gclusters NCB.map_gclusters)
  structure Results = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GResults.results
    fun lens _ = mk_lens NCB.get_results NCB.map_results)
end
end
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base2
    type @{AllT_args} container = @{AllT_args} Z2.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co2.lens x
  end
in
structure Lens2 =
struct
  structure NCB = Base.NCB
  structure GCluster = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GC.gcluster
    fun lens _ = mk_lens NCB.get_gcluster NCB.map_gcluster)
  structure Results = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GResults.results
    fun lens _ = mk_lens NCB.get_results NCB.map_results)
  structure Top_Meta_Vars = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = Top_Meta_Vars.top_meta_vars
    fun lens _ = mk_lens NCB.get_top_meta_vars NCB.map_top_meta_vars)
end
end
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base3
    type @{AllT_args} container = @{AllT_args} Z3.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co3.lens x
  end
in
structure Lens3 =
struct
  structure NCB = Base.NCB
  structure Copy = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = @{AllT_args} copy
    fun lens _ = mk_lens NCB.get_copy NCB.map_copy)
  structure Meta = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = ACMeta.metadata
    fun lens _ = mk_lens NCB.get_meta NCB.map_meta)
end
end
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base4
    type @{AllT_args} container = @{AllT_args} Z4.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co4.lens x
  end
in
structure Lens4 =
struct
  structure NCB = Base.NCB
  structure PAction = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = @{AllT_args} paction
    fun lens _ = mk_lens NCB.get_paction NCB.map_paction)
  structure PResults = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = @{AllT_args} presults
    fun lens _ = mk_lens NCB.get_presults NCB.map_presults)
  structure Action_App_Num = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AANum.action_app_num
    fun lens _ = mk_lens NCB.get_action_app_num NCB.map_action_app_num)
  structure Goal_Focus = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GF.focus
    fun lens _ = mk_lens NCB.get_focus NCB.map_focus)
  structure Meta = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AMeta.metadata
    fun lens _ = mk_lens NCB.get_meta NCB.map_meta)
end
end
local structure Base =
  struct
    open Base
    structure NCB = Node_Co_Base5
    type @{AllT_args} container = @{AllT_args} Z5.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co5.lens x
  end
in
structure Lens5 =
struct
  structure Action_App_Num = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AANum.action_app_num
    fun lens _ = mk_lens NCB.get_action_app_num NCB.map_action_app_num)
  structure Goal_Focus = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GF.focus
    fun lens _ = mk_lens NCB.get_focus NCB.map_focus)
  structure Prio = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = prio
    fun lens _ = mk_lens NCB.get_prio NCB.map_prio)
  structure Meta = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AAMeta.metadata
    fun lens _ = mk_lens NCB.get_result_meta NCB.map_result_meta)
end
end
end

(* pretty printing/shows *)
local
  structure Show = SpecCheck_Show_Base
  fun with_position pretty_position z xs = Pretty.breaks [
      Show.record xs,
      Pretty.block [Pretty.str "at position ", pretty_position z]
    ] |> Pretty.block
in
local
  structure L = Lens1
  fun show z = with_position ZLP.pretty_position1 z
in
structure Show1 = Zippy_Show_Mixin_Base(
  type @{AllT_args} t = @{AllT_args} Z1.zipper
  fun pretty ctxt z = show z [
    ("Goal clusters", GCS.pretty_gclusters ctxt (L.GClusters.getter z)),
    ("Results", GResults.pretty_results (L.Results.getter z))
  ])
end
local
  structure L = Lens2
  fun show z = with_position ZLP.pretty_position2 z
in
structure Show2 = Zippy_Show_Mixin_Base(
  type @{AllT_args} t = @{AllT_args} Z2.zipper
  fun pretty ctxt z = show z [
    ("Goal cluster", GC.pretty_gcluster ctxt (L.GCluster.getter z)),
    ("Results", GResults.pretty_results (L.Results.getter z)),
    ("Top Meta Variables", Top_Meta_Vars.pretty ctxt (L.Top_Meta_Vars.getter z))
  ])
end
local
  structure L = Lens3
  fun show z = with_position ZLP.pretty_position3 z
in
structure Show3 = Zippy_Show_Mixin_Base(
  type @{AllT_args} t = @{AllT_args} Z3.zipper
  fun pretty _ z = show z [
    ("Metadata", ACMeta.pretty_metadata (L.Meta.getter z))
  ])
end
local
  structure L = Lens4
  fun show z = with_position ZLP.pretty_position4 z
in
structure Show4 = Zippy_Show_Mixin_Base(
  type @{AllT_args} t = @{AllT_args} Z4.zipper
  fun pretty _ z = show z [
    ("Action application number", AANum.pretty (L.Action_App_Num.getter z)),
    ("Focus", GF.pretty (L.Goal_Focus.getter z)),
    ("Metadata", AMeta.pretty_metadata (L.Meta.getter z))
  ])
end
local
  structure L = Lens5
  fun show z = with_position ZLP.pretty_position5 z
in
structure Show5 = Zippy_Show_Mixin_Base(
  type @{AllT_args} t = @{AllT_args} Z5.zipper
  fun pretty _ z = show z [
    ("Action application number", AANum.pretty (L.Action_App_Num.getter z)),
    ("Focus", GF.pretty (L.Goal_Focus.getter z)),
    ("Priority", pretty_prio (L.Prio.getter z)),
    ("Metadata", AAMeta.pretty_metadata (L.Meta.getter z))
  ])
end

(* data mixins *)
local structure Base_Mixins =
  struct
    structure Exn = Exn
    structure Co = Co
    structure Ctxt = Ctxt
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} = Show{i}\<close>\<close>
  end
in
(** goal clusters **)
local structure L = Lens1
in
structure Mixin1 =
struct
  structure GClusters = Zippy_Goal_Clusters_Mixin(Zippy_Goal_Clusters_Mixin_Base(
    structure GCS = GCS; structure L = L.GClusters))
  structure Results = Zippy_Goal_Results_Mixin(Zippy_Goal_Results_Mixin_Base(
    structure R = GResults; structure L = L.Results))
end
end

(** goal cluster **)
local structure L = Lens2
in
structure Mixin2 =
struct
  structure GCluster = Zippy_Goal_Cluster_Mixin(Zippy_Goal_Cluster_Mixin_Base(
    structure GC = GC; structure L = L.GCluster))
  structure Results = Zippy_Goal_Results_Mixin(Zippy_Goal_Results_Mixin_Base(
    structure R = GResults; structure L = L.Results))
  structure Top_Meta_Vars = Zippy_Top_Meta_Vars_Mixin(Zippy_Top_Meta_Vars_Mixin_Base(
    structure TMV = Top_Meta_Vars; structure L = L.Top_Meta_Vars))
  structure Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin(
    structure Z = ZL
    structure Goal_Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin_Base(
      structure Top_Meta_Vars = Top_Meta_Vars; structure Results = Results))
end
end

(** goals **)
structure Goals = Zippy_Goals_Mixin_Base(
  structure GClusters = Mixin1.GClusters; structure GCluster = Mixin2.GCluster)
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = ZL; structure Goals = Goals)
structure Goals_Results = Zippy_Goals_Results_Mixin_Base(open Goals
  structure GClusters_Results = Mixin1.Results
  structure GCluster_Results = Mixin2.Results)
structure LGoals_Results = Zippy_Lists_Goals_Results_Mixin(
  structure Z = ZL; structure Goals_Results = Goals_Results)
structure LGoals_Results_TMV = Zippy_Lists_Goals_Results_Top_Meta_Vars_Mixin(
  structure Z = ZL
  structure Goals_Results_Top_Meta_Vars = Zippy_Goals_Results_Top_Meta_Vars_Mixin_Base(
    open Goals_Results; structure Top_Meta_Vars = Mixin2.Top_Meta_Vars))

(** action clusters **)
local structure L = Lens3
in
structure Mixin3 =
struct
  structure Copy = Zippy_Copy_Mixin(open Base_Mixins
    structure Copy = Zippy_Copy_Mixin_Base(
      val parent_logger = logger
      structure FIA = struct
        val full_name = "Zippy.Mixin3.Copy"
        val id = "test_id"
        val pos = @{here}
      end
      structure M = ZB
      structure L = L.Copy
      type @{AllT_args} zipper_to = @{AllT_args} Z1.zipper
      type copy_update_data = copy_update_data
      val copy = Copy
      fun run_copy (Copy copy) = copy)
    structure Show_From = Show3
    structure Show_To = Show1)
  structure ECopy = Zippy_Enum_Copy_Mixin(open Base_Mixins; structure Z = ZE; structure Copy = Copy)
  structure Meta = Zippy_Action_Cluster_Metadata_Mixin_Base(
    structure Meta = ACMeta; structure L = L.Meta)
end
end

(** actions **)
local structure L = Lens4
in
structure Mixin4 =
struct
  structure PAction = Zippy_PAction_Mixin(
    structure PAction = Zippy_PAction_Mixin_Base(
      structure M = MU.MB
      structure L = L.PAction
      structure AResult = AResult
      type @{AllT_args} zipper_expand = @{AllT_args} Z5.zipper
      type @{AllT_args} zipper_trim = @{AllT_args} Z1.zipper
      type prio = prio
      val paction = PAction
      fun run_paction (PAction paction) = paction)
    structure Exn = Exn)

  structure PResults = Zippy_PResults_Mixin(Zippy_PResults_Mixin_Base(open Base_Mixins
    structure M = MU.MB
    structure L = L.PResults
    structure K = ZB.K
    type prio = PAction.prio
    type result = result
    val presults = PResults
    fun dest_presults (PResults presults) = presults))

  structure PResults_Pos = Zippy_PResults_Positions_Mixin(
    structure Z = ZP; structure PResults = PResults)

  structure PAction_PResults = Zippy_PAction_PResults_Mixin(Zippy_PAction_PResults_Mixin_Base(
    structure PResults = PResults; structure PAction = PAction))

  structure Action_App_Num = Zippy_Action_App_Num_Mixin(Zippy_Action_App_Num_Mixin_Base(
    structure AANum = AANum; structure L = L.Action_App_Num))

  structure Goal_Focus = Zippy_Goal_Focus_Mixin_Base(structure F = GF; structure L = L.Goal_Focus)

  structure Meta = Zippy_Action_Cluster_Metadata_Mixin_Base(
    structure Meta = AMeta; structure L = L.Meta)
end
end

(** actions with queues **)
structure PAction_Queue = Zippy_PAction_Queue_Mixin(
  structure Z = ZE
  structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(
    structure PAction = Mixin4.PAction
    structure Queue = Leftist_Heap(type prio = prio; val ord = prio_ord))
  val mk_exn = Library.K exn)

(** action applications **)
local structure L = Lens5
in
structure Mixin5 =
struct
  structure Action_App_Num = Zippy_Action_App_Num_Mixin(Zippy_Action_App_Num_Mixin_Base(
    structure AANum = AANum; structure L = L.Action_App_Num))

  structure Goal_Focus = Zippy_Goal_Focus_Mixin_Base(structure F = GF; structure L = L.Goal_Focus)

  structure Prio = Zippy_Prio_Mixin_Base(type prio = Mixin4.PAction.prio; structure L = L.Prio)

  structure Meta = Zippy_Action_App_Metadata_Mixin(Zippy_Action_App_Metadata_Mixin_Base(
    structure Meta = AAMeta; structure L = L.Meta))
  structure EMeta = Zippy_Enum_Action_App_Metadata_Mixin(structure Z = ZE; structure Meta = Meta)
end
end

(** tactics **)
structure Goals_Tac = Zippy_Goals_Tactic_Mixin_Base(open Goals; structure Tac = Tac)
structure LGoals_Tac = Zippy_Lists_Goals_Tactic_Mixin(
  structure Z = ZL; structure Goals_Tac = Goals_Tac)

structure GTC = Zippy_Goals_Tactic_Copy_Mixin(
  Zippy_Goals_Tactic_Copy_Mixin_Base(open Goals_Tac; structure Copy = Mixin3.Copy))
structure LGTC = Zippy_Lists_Goals_Tactic_Copy_Mixin(open Base_Mixins
  structure Z = ZL; structure GTC = GTC)

structure GTCP = Zippy_Goals_Tactic_Copy_PAction_Mixin_Base(
  open GTC; structure PAction = Mixin4.PAction)
structure LGTCP = Zippy_Lists_Goals_Tactic_Copy_PAction_Mixin(
  structure Z = ZL; structure GTCP = GTCP)

(** runs **)
structure Step = Zippy_Step_Mixin(open Base_Mixins
  structure Z = ZLP
  structure Step = Zippy_Step_Mixin_Base(open LGoals_Results_TMV
    structure PAction_Queue = PAction_Queue)
  val mk_exn = Library.K exn)

structure Run = Zippy_Run_Mixin(open Base_Mixins
  structure Z = ZLP
  structure Run = Zippy_Run_Mixin_Base(open Step; structure Action_App_Meta = Mixin5.Meta)
  val mk_exn = Library.K exn
  type @{AllT_args} state = {ctxt : Proof.context, state : @{ParaT_arg 0}}
  fun seq_from_monad {ctxt, state} =
    State_MSTrans.eval state #> Ctxt_MSTrans.eval ctxt #> the_default Seq.empty
  fun with_state f = Ctxt.with_ctxt (fn ctxt => State.with_state (fn state =>
    f {ctxt = ctxt, state = state})))
end
end
end

end