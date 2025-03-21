(*  Title:      HOCLP/zippy_prover_instance_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_INSTANCE_BASE =
sig
  structure MS : ISTATE_TRANS
  where type ('p1, 'a) mt = 'a option (*FIXME: fixed type only needed to speed up ML compiler*)
  structure AS : IKLEISLI_ARROW_STATE
  where type ('p1, 'i, 'j, 'a) K.M.t = ('p1, 'i, 'j, 'a) MS.t
  structure ME : MONAD_EXCEPTION_BASE
  where type ('p1, 'a) t = (unit, 'p1, 'p1, 'a) MS.t

  structure MDD : KLEISLI_ZIPPY_METADATA_DATA
  where type ('p1, 'a) K.M.t = ('p1, 'a) ME.t
  structure GCSMD : ZIPPY_GOAL_CLUSTERS_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  sharing type GCSMD.L.lens = MDD.L.lens
  structure ACMD : ZIPPY_ACTION_CLUSTER_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  sharing type ACMD.L.lens = MDD.L.lens
  structure AMD : ZIPPY_ACTION_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  sharing type AMD.L.lens = MDD.L.lens
  structure RMD : ZIPPY_RESULT_METADATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) MDD.L.C.cat
  where type metadata = Zippy_Result_Metadata.metadata
  where type progress = Zippy_Result_Metadata.progress
  sharing type RMD.L.lens = MDD.L.lens

  structure P : PRIO
  where type prio = Prio.prio

  include ZIPPY_PROVER_WITH_POSITION
  where type @{T_args} gcsd_more = (GCSMD.metadata, unit) MDD.metadata_data
  where type @{T_args} gcd_more = unit
  where type @{T_args} cd_more = (ACMD.metadata, unit) MDD.metadata_data
  where type @{T_args} action_fd_more = (AMD.metadata, unit) MDD.metadata_data
  where type @{T_args} rdd_more = unit
  where type rd_more = RMD.metadata
  where type ('p1, 'a) M.t = ('p1, 'a) ME.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) MDD.L.lens
  where type prio = P.prio
  (*FIXME: only needed to speed up ML compiler*)
  where type 'a ZPOS.Z.LI.t = 'a list

  (*FIXME: only needed to speed up ML compiler*)
  val init_state' :  (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat ->
    (@{ParaT_args}, GCS.state, (focus -> (int * focus) list) * @{T_args} Z1.zipper) cat
end

functor Zippy_Prover_Instance_Base(
    M : MONAD_EXCEPTION_BASE
    where type ('p1, 'a) t = 'a option
    where type 'p1 exn = unit
  ) :> (*FIXME: abstraction of types only needed to speed up ML compiler*)
    ZIPPY_PROVER_INSTANCE_BASE
  =
struct

structure ME = M
structure MS = IState_Trans(
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
structure GCSMD = Lift_Zippy_Goal_Clusters_Metadata(
  open Base; structure GCSMD = Zippy_Goal_Clusters_Metadata)
structure ACMD = Lift_Zippy_Action_Cluster_Metadata(
  open Base; structure ACMD = Zippy_Action_Cluster_Metadata)
structure AMD = Lift_Zippy_Action_Metadata(open Base; structure AMD = Zippy_Action_Metadata)
structure RMD = Lift_Zippy_Result_Metadata(open Base; structure RMD = Zippy_Result_Metadata)

structure Z = Instantiate_Zippy_Prover_With_Position(
  structure Z = Z
  type @{T_args} inst1 = (GCSMD.metadata, unit) MDD.metadata_data
  type @{T_args} inst2 = unit
  type @{T_args} inst3 = (ACMD.metadata, unit) MDD.metadata_data
  type @{T_args} inst4 = (AMD.metadata, unit) MDD.metadata_data
  type @{T_args} inst5 = unit)
open Z

local structure M = Monad(Z.M) open M
in
fun init_state' mk_gcdm state =
  GCSMD.metadata false
  >>= (fn m => MDD.metadata_data (m, ())
  >>= (fn gcsdm => Z.init_state
    (arr (rpair (Z.no_parent ()) #> rpair ((), Z.no_parent ()) #> rpair 0))
    gcsdm mk_gcdm state))
end

end
