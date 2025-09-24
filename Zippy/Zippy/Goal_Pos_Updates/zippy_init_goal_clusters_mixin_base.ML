(*  Title:      Zippy/zippy_init_goal_clusters_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INIT_GOAL_CLUSTERS_MIXIN_BASE =
sig
  include ZIPPY_GOALS_POS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>

  (*initialise some data (e.g. add an action cluster) for the given goal cluster with the given focus*)
  type init_gcluster = GPU.F.focus -> (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph
  structure Data : GENERIC_TABLE_DATA
  where type key = Zippy_Identifier.id
  (*performance optimisation: additionally pass goal state and subgoals data
  (binders, (premises, conclusion)) since most actions in practice depend on that data*)
  where type value = GClusters.GCS.state * ((string * typ) list * (term list * term)) list ->
    init_gcluster
end

functor Zippy_Init_Goal_Clusters_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_POS_MIXIN_BASE
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  end) : ZIPPY_INIT_GOAL_CLUSTERS_MIXIN_BASE
  =
struct

open A A.M
structure FI = Functor_Instance(FI)

type init_gcluster = GPU.F.focus -> (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph

\<^functor_instance>\<open>struct_name: Data
  functor_name: Generic_Table_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Log.logger
    type key = Zippy_Identifier.id
    val pretty_key = Zippy_Identifier.pretty
    val ord_key = Zippy_Identifier.ord
    type value = Zippy_Thm_State.state * ((string * typ) list * (term list * term)) list ->
      init_gcluster
    val pretty_value = Library.K (Library.K (Pretty.str "<init goal cluster morphism>"))\<close>\<close>

end
