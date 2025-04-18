(*  Title:      Zippy/gen_zippy_prover_base.ML
    Author:     Kevin Kappelmann
*)
signature GEN_ZIPPY_PROVER_BASE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  structure GC : ZIPPY_GOAL_CLUSTER
  sharing type GC.GCS.gclusters = GCS.gclusters
  sharing type GC.GCS.gcpos = GCS.gcpos
  structure F : ZIPPY_FOCUS
  sharing type F.GCS.gclusters = GCS.gclusters
  sharing type F.GCS.gcpos = GCS.gcpos
  structure RD : KLEISLI_ZIPPY_RESULT_DATA
  structure RDD : ZIPPY_RESULT_DATA_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) RD.L.C.cat
  sharing type RDD.L.lens = RD.L.lens
  type @{AllT_args} rdd_more

  structure T : ZIPPY_TACTIC
  sharing type T.RD.result_data = RD.result_data
  sharing type T.GPU.GCS.gcpos = GCS.gcpos
  sharing type T.GPU.GCS.gclusters = GCS.gclusters
  sharing type T.GPU.F.focus = F.focus
  sharing type T.GC.gcluster = GC.gcluster

  type rd_more
  type result_data = rd_more T.result_data

  include ZIPPY_WITH_GOALS
  where type gclusters = GCS.gclusters
  where type gcluster = GC.gcluster
  where type focus = F.focus
  where type copy_update_data = F.focus -> (GCS.cluster_pos * F.focus) list
  where type result = (result_data, T.update_data) T.RUD.result_update_data
  where type @{AllT_args} actiona_fd_more = (result_data, @{AllT_args} rdd_more) RDD.result_data_data
  where type @{ParaT_args encl = "(" ")"} AE.exn = unit
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) RD.K.M.t
  where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) RD.L.lens
end

functor Gen_Zippy_Prover_Base(
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure GC : ZIPPY_GOAL_CLUSTER
    sharing type GC.GCS.gcpos = GCS.gcpos
    sharing type GC.GCS.gclusters = GCS.gclusters
    structure F : ZIPPY_FOCUS
    sharing type F.GCS.gcpos = GCS.gcpos
    sharing type F.GCS.gclusters = GCS.gclusters
    structure RDD : KLEISLI_ZIPPY_RESULT_DATA_DATA
    type @{AllT_args} rdd_more
    structure T : ZIPPY_TACTIC
    sharing type T.GC.GCS.gcpos = GCS.gcpos
    sharing type T.GC.GCS.gclusters = GCS.gclusters
    sharing type T.GC.gcluster = GC.gcluster
    sharing type T.GPU.F.focus = F.focus
    type rd_more
    structure Z : ZIPPY_WITH_GOALS
    where type gclusters = GCS.gclusters
    where type gcluster = GC.gcluster
    where type focus = F.focus
    where type copy_update_data = F.focus -> (GCS.cluster_pos * F.focus) list
    where type result = (rd_more T.result_data, T.update_data) T.RUD.result_update_data
    where type @{AllT_args} actiona_fd_more = @{ZipperT_arg 4}
    where type @{ParaT_args encl = "(" ")"} AE.exn = unit
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) RDD.K.M.t
    where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) RDD.L.lens
  ) : GEN_ZIPPY_PROVER_BASE =
struct

structure GCS = GCS
structure GC = GC
structure F = F
structure RDD = RDD
type @{AllT_args} rdd_more = @{AllT_args} rdd_more
structure RD = Lift_Zippy_Result_Data(
  structure RD = T.RD
  structure AF = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply" ^ ".A"\<close>
  structure AT = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M)
  structure L = Z.L
  fun lift f = AT.arr f)
structure T = T
type rd_more = rd_more
type result_data = rd_more T.result_data

open Z
structure Z = Instantiate_Zippy_With_Goals(
  \<^imap>\<open>\<open>{i}\<close> =>
  \<open>type @{AllT_args} inst{i} = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
  type @{AllT_args} inst5 = (result_data, @{AllT_args} rdd_more) RDD.result_data_data
  structure Z = Z
)
open Z

end

functor Instantiate_Gen_Zippy_Prover_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : GEN_ZIPPY_PROVER_BASE
  ) :
    GEN_ZIPPY_PROVER_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZM.container
    where type @{AllT_args} ZCORE.A.Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.content
    where type @{AllT_args} ZCORE.A.Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.zcontext
    where type @{AllT_args} ZCORE.A.Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.zipper\<close>\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.zcontext{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.zcontext{i}
    where type @{AllT_args} ZCORE.pzipper{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.pzipper{i}\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{AllT_args} Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type @{AllT_args} gcsd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.gcsd_more
    where type @{AllT_args} gcd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.gcd_more
    where type @{AllT_args} cd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{AllT_args} action_fd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.action_fd_more
    where type @{AllT_args} rdd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.rdd_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{AllT_args} presults = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_Goals_Base(open Base; structure Z = Z)
open Z
end
