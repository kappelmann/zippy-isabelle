(*  Title:      Zippy/zippy_instance_auto.ML
    Author:     Kevin Kappelmann
*)
functor Zippy_Instance_Auto(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_RESOLVE
    structure TI : TERM_INDEX
    val resolve_init_args : (int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLP.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      Z.Base_Data.AAMeta.P.progress,
      @{AllT_args} Z.PResults.prio_sq_co,
      term * @{AllT_args} Z.Resolve.data -> bool) Zippy_Instance_Resolve_Data_Args.PCA.entries
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) =
struct
structure FI =  Functor_Instance(FI)
structure Logging =
struct
  val logger = Logger.setup_new_logger zippy_base_logger FI.name
  structure Init_Goal_Clusters = Zippy_Logger_Mixin_Base(val parent_logger = logger
    val name = "Init_Goal_Clusters")
end

\<^functor_instance>\<open>struct_name: Resolves
  functor_name: Zippy_Instance_Resolves_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = Discrimination_Tree
    val init_args = resolve_init_args
    structure Log = Logging\<close>\<close>

local
  open Z
  structure Goals = Zippy_Goals_Mixin_Base(
    structure GClusters = Mixin1.GClusters; structure GCluster = Mixin2.GCluster)
  structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU)
in
structure Init_Goal_Clusters = Zippy_Init_Goal_Clusters_Mixin(
  structure Z = Zippy_Enum_Mixin(Zippy_Enum_Mixin_Base(structure Z = ZLP; structure Co = Co))
  structure IGC = \<^functor_instance>\<open>
    functor_name: Zippy_Init_Goal_Clusters_Mixin_Base
    id: \<open>FI.prefix_id "init_gcs"\<close>
    path: \<open>FI.struct_op "Init_Goal_Clusters"\<close>
    more_args: \<open>open Goals_Pos
      structure M = Z
      structure Log = Logging.Init_Goal_Clusters\<close>\<close>
  structure Ctxt = Ctxt)
end
end
