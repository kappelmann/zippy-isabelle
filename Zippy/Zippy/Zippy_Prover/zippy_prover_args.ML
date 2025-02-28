(*  Title:      HOCLP/zippy_prover_args.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_ARGS =
sig
  structure ZGCS : \<^eval>\<open>T_Args.suffix_Poly_nargs "SINGLE_CONTENT_ZIPPER"\<close>

  structure ZGC : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = unit
  sharing type ZGC.M.t = ZGCS.M.t
  sharing type ZGC.ZO.L.lens = ZGCS.ZO.L.lens

  structure ZAC : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZGC.LI.M.exn
  sharing type ZAC.M.t = ZGCS.M.t
  sharing type ZAC.ZO.L.lens = ZGCS.ZO.L.lens

  structure ZA : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZGC.LI.M.exn
  sharing type ZA.M.t = ZGCS.M.t
  sharing type ZA.ZO.L.lens = ZGCS.ZO.L.lens

  structure ZAA : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZGC.LI.M.exn
  sharing type ZAA.M.t = ZGCS.M.t
  sharing type ZAA.ZO.L.lens = ZGCS.ZO.L.lens

  include ZIPPY_PROVER_BASE_UTIL
  where type @{T_args} A.Z1.ZM.container = @{T_args} ZGCS.ZM.container
  where type @{T_args} A.Z2.ZM.container = @{T_args} ZGC.ZM.container
  where type @{T_args} A.Z3.ZM.container = @{T_args} ZAC.ZM.container
  where type @{T_args} A.Z4.ZM.container = @{T_args} ZA.ZM.container
  where type @{T_args} A.Z5.ZM.container = @{T_args} ZAA.ZM.container
  where type @{T_args} A.Z1.ZO.content = @{T_args} ZGCS.ZO.content
  where type @{T_args} A.Z2.ZO.content = @{T_args} ZGC.ZO.content
  where type @{T_args} A.Z3.ZO.content = @{T_args} ZAC.ZO.content
  where type @{T_args} A.Z4.ZO.content = @{T_args} ZA.ZO.content
  where type @{T_args} A.Z5.ZO.content = @{T_args} ZAA.ZO.content
  where type @{T_args} A.Z1.ZO.zcontext = @{T_args} ZGCS.ZO.zcontext
  where type @{T_args} A.Z2.ZO.zcontext = @{T_args} ZGC.ZO.zcontext
  where type @{T_args} A.Z3.ZO.zcontext = @{T_args} ZAC.ZO.zcontext
  where type @{T_args} A.Z4.ZO.zcontext = @{T_args} ZA.ZO.zcontext
  where type @{T_args} A.Z5.ZO.zcontext = @{T_args} ZAA.ZO.zcontext
  where type 'p1 CO.AE.exn = 'p1 ZGC.LI.M.exn
  sharing type M.t = ZGCS.M.t
  sharing type L.lens = ZGCS.ZO.L.lens
end

functor Zippy_Prover_Args(
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val parent_logger : Logger.logger_binding
    structure LZ : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type @{T_args} content = @{PolyT_arg 0}
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = unit
    structure CO : COROUTINE_UTIL_APPLY
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) LZ.cat
    where type 'p1 AE.exn = 'p1 LZ.LI.M.exn
  ) : ZIPPY_PROVER_ARGS =
struct

structure AE = Kleisli_Arrow_Exception(LZ.LI.M)
structure L = LZ.ZO.L

structure ZGCS = \<^eval>\<open>T_Args.suffix_Poly_nargs "Single_Content_Zipper"\<close>(
  structure AE = AE
  structure L = L
  type @{T_args} content = @{PolyT_arg 0}
)
structure ZGC = LZ
structure ZAC = LZ
structure ZA = LZ
structure ZAA = LZ

structure AZ = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes"\<close>(
  structure A = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} ncontent{i} = \<^eval>\<open>implode ["@{PolyT_arg ", string_of_int ({i} - 1), "}"]\<close>\<close>\<close>
    structure Z1 = ZGCS
    structure Z2 = ZGC
    structure Z3 = ZAC
    structure Z4 = ZA
    structure Z5 = ZAA
  )
  structure ZD = Zipper_Data
)

structure FIU = Functor_Instance_Util(FIA)
@{functor_instance struct_name = GCS
  and functor_name = Zippy_Goal_Clusters
  and accessor = FIU.accessor
  and id = FIU.FIA.id
  and more_args = \<open>structure UF = Imperative_Union_Find; val parent_logger = parent_logger\<close>}
structure GC = Zippy_Goal_Cluster(GCS)
structure F = Zippy_Focus(GCS)

structure Base =
struct
  structure AF = SArrow_Arrow_Apply.A
  structure AT = Kleisli_Arrow(AE.K.M)
  structure L = L
  fun lift f = AT.arr f
end

structure Z = Zippy_With_PAction_Util(
  structure CO = CO
  structure Z = Zippy_With_PAction(
    type copy_update_data = F.focus -> (GCS.cluster_pos * F.focus) list
    type prio = Prio.prio
    structure CD = Lift_Zippy_Copy_Data(open Base; structure CD = Zippy_Copy_Data)
    type @{T_args} cd_more = @{PolyT_arg 2}
    structure PAD = Lift_Zippy_PAction_Data(open Base; structure PAD = Zippy_PAction_Data)
    type @{T_args} pad_more = @{PolyT_arg 3}
    structure PD = Lift_Zippy_Prio_Data(open Base; structure PD = Zippy_Prio_Data)
    type @{T_args} pd_more = @{PolyT_arg 4}
    structure Z = AZ))

structure Z = Zippy_With_PResults_Util(
  structure Z = Zippy_With_PResults(
    type result = unit
    structure PRD = Lift_Zippy_PResults_Data(open Base; structure PRD = Zippy_PResults_Data)
    structure AND = Lift_Zippy_Actiona_Num_Data(open Base; structure AND = Zippy_Actiona_Num_Data)
    type @{T_args} action_and_more = @{PolyT_arg 3}
    type @{T_args} actiona_and_more = @{PolyT_arg 4}
    structure Z = Z))

structure Z = Zippy_With_Goals_Util(
  structure Z = Zippy_With_Goals(
    type gclusters = GCS.gclusters
    type gcluster = GC.gcluster
    type focus = F.focus
    structure GCSD = Lift_Zippy_GClusters_Data(open Base; structure GCSD = Zippy_GClusters_Data)
    type @{T_args} gcsd_more = @{PolyT_arg 0}
    structure GCD = Lift_Zippy_GCluster_Data(open Base; structure GCD = Zippy_GCluster_Data)
    type @{T_args} gcd_more = @{PolyT_arg 1}
    structure FD = Lift_Zippy_Focus_Data(open Base; structure FD = Zippy_Focus_Data)
    type @{T_args} action_fd_more = @{PolyT_arg 3}
    type @{T_args} actiona_fd_more = @{PolyT_arg 4}
    structure Z = Z))

structure Z = Zippy_Prover_Base_Util(
  structure Z = Zippy_Prover_Base(
    structure GCS = GCS
    structure GC = GC
    structure F = F
    structure Z = Z)
  structure TR = Zippy_Tactic_Result(
    structure RD = Zippy_Result_Data
    structure RUD = Zippy_Result_Update_Data
    structure GPU = Zippy_GPos_Update_Util(
      structure F = Z.F
      structure GPU = Zippy_GPos_Update(
        structure GCS = Z.GCS
        structure T = Zippy_GPos_Update_Target))
    structure GC = Z.GC))

structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = unit\<close>\<close> end
structure ZGCS = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Content_Zipper"\<close>(
  open Base
  type @{T_args} inst1 = @{T_args} Z.N1.node
  structure Z = ZGCS
)
structure ZGC = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base
  type @{T_args} inst1 = @{T_args} Z.N2.node
  structure Z = ZGC
)
structure ZAC = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base
  type @{T_args} inst1 = @{T_args} Z.N3.node
  structure Z = ZAC
)
structure ZA = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base
  type @{T_args} inst1 = @{T_args} Z.N4.node
  structure Z = ZA
)
structure ZAA = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base
  type @{T_args} inst1 = @{T_args} Z.N5.node
  structure Z = ZAA
)
open Z

end
