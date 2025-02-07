(*  Title:      HOCLP/zippy_prover_args.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_ARGS =
sig
  structure ZGCS : SINGLE_CONTENT_ZIPPER4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) content = 'a1

  structure ZGC : LIST_ZIPPER4
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = unit
  sharing type ZGC.M.t = ZGCS.M.t
  sharing type ZGC.ZO.L.lens = ZGCS.ZO.L.lens

  structure ZACT : ROSE_ZIPPER4
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZGC.LI.M.exn
  sharing type ZACT.M.t = ZGCS.M.t
  sharing type ZACT.ZO.L.lens = ZGCS.ZO.L.lens

  type ('p1, 'a1, 'a2, 'a3, 'a4) node1
  type ('p1, 'a1, 'a2, 'a3, 'a4) node2
  type ('p1, 'a1, 'a2, 'a3, 'a4) node3
  type ('p1, 'a1, 'a2, 'a3, 'a4) node4

  structure AZN : ALTERNATING_ZIPPERS4_NODES
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N1.node = ('p1, 'a1, 'a2, 'a3, 'a4) node1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N1.content = 'a1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z1.ZM.container =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node1, 'a2, 'a3, 'a4) ZGCS.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z1.ZO.zcontext =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node1, 'a2, 'a3, 'a4) ZGCS.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N2.node = ('p1, 'a1, 'a2, 'a3, 'a4) node2
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N2.content = 'a2
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z2.ZM.container =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node2, 'a2, 'a3, 'a4) ZGC.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z2.ZO.zcontext =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node2, 'a2, 'a3, 'a4) ZGC.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N3.node = ('p1, 'a1, 'a2, 'a3, 'a4) node3
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N3.content = 'a3
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z3.ZM.container =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node3, 'a2, 'a3, 'a4) ZACT.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z3.ZO.zcontext =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node3, 'a2, 'a3, 'a4) ZACT.ZO.zcontext
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N4.node = ('p1, 'a1, 'a2, 'a3, 'a4) node4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) N4.content = 'a4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z4.ZM.container =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node4, 'a2, 'a3, 'a4) ZACT.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) A.Z4.ZO.zcontext =
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node4, 'a2, 'a3, 'a4) ZACT.ZO.zcontext
  sharing type AZN.M.t = ZGCS.M.t

  include ZIPPY_PROVER_BASE_UTIL
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.Z1.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.Z2.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.Z3.ZM.container
  where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.Z4.ZM.container
  sharing type M.t = AZN.M.t
  sharing type L.lens = AZN.L.lens
  sharing type Z1.zipper = AZN.Z1.zipper
  sharing type Z1.ZO.content = AZN.Z1.ZO.content
  sharing type Z1.ZO.zcontext = AZN.Z1.ZO.zcontext
  sharing type Z2.zipper = AZN.Z2.zipper
  sharing type Z2.ZO.content = AZN.Z2.ZO.content
  sharing type Z2.ZO.zcontext = AZN.Z2.ZO.zcontext
  sharing type Z3.zipper = AZN.Z3.zipper
  sharing type Z3.ZO.content = AZN.Z3.ZO.content
  sharing type Z3.ZO.zcontext = AZN.Z3.ZO.zcontext
  sharing type Z4.zipper = AZN.Z4.zipper
  sharing type Z4.ZO.content = AZN.Z4.ZO.content
  sharing type Z4.ZO.zcontext = AZN.Z4.ZO.zcontext
end

functor Zippy_Prover_Args(
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val parent_logger : Logger.logger_binding
    structure ZGC : LIST_ZIPPER4
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = unit
    structure ZACT : ROSE_ZIPPER4
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = 'p1 ZGC.LI.M.exn
    sharing type ZACT.M.t = ZGC.M.t
    sharing type ZACT.ZO.L.lens = ZGC.ZO.L.lens
  ) : ZIPPY_PROVER_ARGS =
struct

structure ZGC = ZGC
structure ZACT = ZACT
structure ZGCS = Single_Content_Zipper4(
  structure AE = Kleisli_Arrow_Exception(ZGC.LI.M)
  structure L = ZGC.ZO.L
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = 'a1
)

structure AZN = Alternating_Zippers4_Nodes(
  structure A = Alternating_Zippers4_Nodes_Base_Args_Simple_Zippers(
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1 = 'a1
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2 = 'a2
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3 = 'a3
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4 = 'a4
    structure Z1 = ZGCS
    structure Z2 = ZGC
    structure Z3 = ZACT
    structure Z4 = ZACT
  )
  structure ZD = Zipper_Data
)
type ('p1, 'a1, 'a2, 'a3, 'a4) node1 = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N1.node
type ('p1, 'a1, 'a2, 'a3, 'a4) node2 = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N2.node
type ('p1, 'a1, 'a2, 'a3, 'a4) node3 = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N3.node
type ('p1, 'a1, 'a2, 'a3, 'a4) node4 = ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N4.node

structure FIU = Functor_Instance_Util(FIA)
@{functor_instance struct_name = GCS
  and functor_name = Zippy_Goal_Clusters
  and accessor = FIU.accessor
  and id = FIU.FIA.id
  and more_args = \<open>structure UF = Imperative_Union_Find; val parent_logger = parent_logger\<close>}

local structure M = ZGC.LI.M; structure A = Kleisli_Arrow(M)
in
structure Base =
struct
  structure AF = SArrow_Arrow_Apply.A
  structure AT = A
  structure L = ZGC.ZO.L
  fun lift f = AT.arr f
end
structure Z = Zippy_Prover_Base(
  structure Z = Zippy_With_Goals(
    structure Z = Zippy_With_Result(
      structure Z = Zippy_With_PAction(
        structure PAD = Lift_Zippy_PAction_Data(open Base; structure AD = Zippy_PAction_Data)
        structure CD = Lift_Zippy_Copy_Data(open Base; structure CD = Zippy_Copy_Data)
        structure AZ = AZN
      )
      structure RD = Lift_Zippy_Result_Data(open Base; structure RD = Zippy_Result_Data)
    )
    structure GCSD =
      Lift_Zippy_Goal_Clusters_Data(open Base; structure GCSD = Zippy_Goal_Clusters_Data)
    structure GCD =
      Lift_Zippy_Goal_Cluster_Data(open Base; structure GCD = Zippy_Goal_Cluster_Data)
    structure FD = Lift_Zippy_Focus_Data(open Base; structure FD = Zippy_Focus_Data)
  )
  structure GCS = GCS
  structure GC = Zippy_Goal_Cluster(GCS)
  structure F = Zippy_Focus(GCS)
  structure AND = Lift_Zippy_Action_Num_Data(open Base; structure AND = Zippy_Action_Num_Data)
  structure CO = Coroutine(A)
)

structure Z = Zippy_Prover_Base_Util(
  structure Z = Z
  structure AU = Zippy_Action_Util(
    structure AE = Kleisli_Arrow_Exception_Rec(Kleisli_Arrow_Exception(M))
    structure CO = Z.CO
  )
  structure TR = Zippy_Tactic_Result(
    structure RUD = Zippy_Result_Update_Data
    structure GPU = Zippy_GPos_Update_Util(
      structure GPU = Zippy_GPos_Update(
        structure GCS = Z.GCS
        structure T = Zippy_GPos_Update_Target)
      structure F = Z.F)
    structure GC = Z.GC))
open Z
end

end
