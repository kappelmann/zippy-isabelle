(*  Title:      HOCLP/zippy_prover_instance_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_INSTANCE_BASE =
sig
  structure MS : STATE_TRANS
  structure AS : IKLEISLI_ARROW_STATE
  where type ('p1, 'i, 'j, 'a) K.M.t = ('p1, 'i, 'j, 'a) MS.t
  structure ME : MONAD_EXCEPTION_BASE
  where type ('p1, 'a) t = (unit, 'p1, 'p1, 'a) MS.t

  structure MDD : KLEISLI_ZIPPY_METADATA_DATA
  where type ('p1, 'a) K.M.t = ('p1, 'a) ME.t
  structure ACMD : ZIPPY_ACTION_CLUSTER_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  sharing type ACMD.L.lens = MDD.L.lens
  structure AMD : ZIPPY_ACTION_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  sharing type AMD.L.lens = MDD.L.lens
  structure RMD : ZIPPY_RESULT_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  sharing type RMD.L.lens = MDD.L.lens

  structure P : PRIO
  where type prio = Prio.prio

  include ZIPPY_PROVER_WITH_POSITION
  where type @{T_args} gcsd_more = unit
  where type @{T_args} gcd_more = unit
  where type @{T_args} cd_more = (ACMD.metadata, unit) MDD.metadata_data
  where type @{T_args} action_fd_more = (AMD.metadata, unit) MDD.metadata_data
  where type @{T_args} rdd_more = unit
  where type rd_more = RMD.metadata
  where type ('p1, 'a) M.t = ('p1, 'a) ME.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) MDD.L.lens
  where type prio = P.prio
end

functor Zippy_Prover_Instance_Base(
    M : MONAD_EXCEPTION_BASE
    where type 'p1 exn = unit
  ) :
    ZIPPY_PROVER_INSTANCE_BASE
  =
struct

structure ME = M
structure MS = State_Trans(
  structure M = ME
  structure SR = Pair_State_Result_Base)
structure ME = IMonad_Exception_State_Trans(structure M = ME; structure S = MS)
structure ME : MONAD_EXCEPTION_BASE = struct open ME type ('p1, 'a) t = (unit, 'p1, 'p1, 'a) t end
structure AS = IKleisli_Arrow_State(MS)

structure P = Prio

structure Z = Zippy_Prover_With_Position(Zippy_Prover_With_Position_Base(
  structure M = ME
  type prio = Prio.prio
  type rd_more = Zippy_Result_Metadata.metadata))

structure Base =
struct
  structure AF = SArrow_Arrow_Apply.A
  structure AT = Kleisli_Arrow(Z.AE.K.M)
  structure L = Z.L
  fun lift f = AT.arr f
end

structure MDD = Lift_Zippy_Metadata_Data(open Base; structure MDD = Zippy_Metadata_Data)
structure ACMD = Lift_Zippy_Action_Cluster_Metadata(
  open Base; structure ACMD = Zippy_Action_Cluster_Metadata)
structure AMD = Lift_Zippy_Action_Metadata(open Base; structure AMD = Zippy_Action_Metadata)
structure RMD = Lift_Zippy_Result_Metadata(open Base; structure RMD = Zippy_Result_Metadata)

structure Z = Instantiate_Zippy_Prover_With_Position(
  structure Z = Z
  type @{T_args} inst1 = unit
  type @{T_args} inst2 = unit
  type @{T_args} inst3 = (ACMD.metadata, unit) MDD.metadata_data
  type @{T_args} inst4 = (AMD.metadata, unit) MDD.metadata_data
  type @{T_args} inst5 = unit)
open Z

end

functor Instantiate_Zippy_Prover_Instance_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER_INSTANCE_BASE
  ) :
    ZIPPY_PROVER_INSTANCE_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.zipper\<close>
      where start = 2\<close>
    where type ('p1, 'a) MS.mt = ('p1, 'a) Z.MS.mt
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCORE.zcontext{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.zcontext{i}
    where type @{T_args} ZCORE.pzipper{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.pzipper{i}\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{T_args} Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{T_args} Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{T_args} Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{T_args} presults = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_Prover_With_Position(open Base; structure Z = Z)
open Z
end

