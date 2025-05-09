(*  Title:      Zippy/zippy_goal_cluster_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_MIXIN_BASE =
sig
  structure GC : ZIPPY_GOAL_CLUSTER

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = GC.gcluster
end

functor Zippy_Goal_Cluster_Mixin_Base(
    L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 1}
  ) :
  sig
    structure DataM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} data = Standard_Zippy_Goal_Cluster.gcluster
    where type @{AllT_args} more = @{AllT_args} L.data

    include ZIPPY_GOAL_CLUSTER_MIXIN_BASE
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT (ML_Gen.AllT_args () ^ " DataM.data_more") 2\<close>) L.container
    structure DataM_More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} DataM.more
  end
  =
struct

structure GC = Standard_Zippy_Goal_Cluster

type @{AllT_args} container = (@{ParaT_args}
  @{ZipperT_args stop = 0},
  (GC.gcluster, @{ZipperT_arg 1}) Data_MoreT.data_more,
  @{ZipperT_args start = 2}) L.container

structure DataM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  type @{AllT_args} data = GC.gcluster
  type @{AllT_args} more = @{AllT_args} L.data)

structure Base =
struct
  type @{AllT_args} container = @{AllT_args} container
  fun mk_lens l = L.comp l (L.lens ())
end
structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} DataM.data
  fun lens _ = mk_lens (DataM.Data.lens ()))
structure DataM_More = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} DataM.more
  fun lens _ = mk_lens (DataM.More.lens ()))

end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Instantiate_Zippy_Goal_Cluster_Mixin_Base_{j}(
    type @{AllT_args} inst
    structure GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  ) :
    ZIPPY_GOAL_CLUSTER_MIXIN_BASE
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) GCluster.L.container
  =  GCluster\<close>\<close>


