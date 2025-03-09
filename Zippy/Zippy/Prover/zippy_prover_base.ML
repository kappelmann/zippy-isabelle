(*  Title:      HOCLP/zippy_prover_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_BASE =
sig
  structure ZCOREAZ1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "SINGLE_CONTENT_ZIPPER"\<close>

  structure ZCOREAZ2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = unit
  sharing type ZCOREAZ2.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ2.ZO.L.lens = ZCOREAZ1.ZO.L.lens

  structure ZCOREAZ3 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZCOREAZ2.LI.M.exn
  sharing type ZCOREAZ3.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ3.ZO.L.lens = ZCOREAZ1.ZO.L.lens

  structure ZCOREAZ4 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZCOREAZ2.LI.M.exn
  sharing type ZCOREAZ4.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ4.ZO.L.lens = ZCOREAZ1.ZO.L.lens

  structure ZCOREAZ5 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  where type 'p1 LI.M.exn = 'p1 ZCOREAZ2.LI.M.exn
  sharing type ZCOREAZ5.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ5.ZO.L.lens = ZCOREAZ1.ZO.L.lens

  include GEN_ZIPPY_PROVER
  where type @{T_args} ZCORE.A.Z1.ZM.container = @{T_args} ZCOREAZ1.ZO.content
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{T_args} ZCORE.A.Z{i}.ZM.container = @{T_args} ZCOREAZ{i}.ZM.container\<close>
  where start = 1\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{T_args} ZCORE.A.Z{i}.ZO.content = @{T_args} ZCOREAZ{i}.ZO.content
  where type @{T_args} ZCORE.A.Z{i}.ZO.zcontext = @{T_args} ZCOREAZ{i}.ZO.zcontext\<close>\<close>
  sharing type M.t = ZCOREAZ1.M.t
  sharing type L.lens = ZCOREAZ1.ZO.L.lens
end

functor Zippy_Prover_Base(
    structure ZCOREAZ1 : \<^eval>\<open>T_Args.suffix_Poly_nargs "SINGLE_CONTENT_ZIPPER"\<close>

    structure ZCOREAZ2 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = unit
    sharing type ZCOREAZ2.M.t = ZCOREAZ1.M.t
    sharing type ZCOREAZ2.ZO.L.lens = ZCOREAZ1.ZO.L.lens

    structure ZCOREAZ3 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = 'p1 ZCOREAZ2.LI.M.exn
    sharing type ZCOREAZ3.M.t = ZCOREAZ1.M.t
    sharing type ZCOREAZ3.ZO.L.lens = ZCOREAZ1.ZO.L.lens

    structure ZCOREAZ4 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = 'p1 ZCOREAZ2.LI.M.exn
    sharing type ZCOREAZ4.M.t = ZCOREAZ1.M.t
    sharing type ZCOREAZ4.ZO.L.lens = ZCOREAZ1.ZO.L.lens

    structure ZCOREAZ5 : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type 'a LI.t = 'a list
    where type 'p1 LI.M.exn = 'p1 ZCOREAZ2.LI.M.exn
    sharing type ZCOREAZ5.M.t = ZCOREAZ1.M.t
    sharing type ZCOREAZ5.ZO.L.lens = ZCOREAZ1.ZO.L.lens

    structure ZCORE : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} N{i}.content = @{PolyT_arg \<open>{i} - 1\<close>}\<close>\<close>
    where type @{T_args} A.Z1.ZM.container = @{T_args} ZCOREAZ1.ZO.content
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.Z{i}.ZM.container = @{T_args} ZCOREAZ{i}.ZM.container\<close>
    where start = 1\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.Z{i}.ZO.content = @{T_args} ZCOREAZ{i}.ZO.content
    where type @{T_args} A.Z{i}.ZO.zcontext = @{T_args} ZCOREAZ{i}.ZO.zcontext\<close>\<close>
    sharing type ZCORE.M.t = ZCOREAZ1.M.t
    sharing type ZCORE.L.lens = ZCOREAZ1.ZO.L.lens

    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
    sharing type Z.M.t = ZCORE.M.t
    sharing type Z.L.lens = ZCORE.L.lens

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val zcore_content{i} : unit ->
      (@{ParaT_args}, @{T_args} Z.Z{i}.ZO.content, @{T_args} ZCORE.Z{i}.ZO.content) Z.L.slens\<close>\<close>

    structure CO : COROUTINE_UTIL_APPLY
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) Z.cat
    where type 'p1 AE.exn = 'p1 ZCOREAZ2.LI.M.exn

    type prio
    type rd_more
  ) :
    ZIPPY_PROVER_BASE
    where type @{T_args} gcsd_more = @{PolyT_arg 0}
    where type @{T_args} gcd_more = @{PolyT_arg 1}
    where type @{T_args} cd_more = @{PolyT_arg 2}
    where type @{T_args} action_fd_more = @{PolyT_arg 3}
    where type @{T_args} rdd_more = @{PolyT_arg 4}
    where type prio = prio
    where type rd_more = rd_more
  =
struct

structure ZCOREAZ1 = ZCOREAZ1
structure ZCOREAZ2 = ZCOREAZ2
structure ZCOREAZ3 = ZCOREAZ3
structure ZCOREAZ4 = ZCOREAZ4
structure ZCOREAZ5 = ZCOREAZ5

structure AE = Kleisli_Arrow_Exception(ZCOREAZ2.LI.M)
structure L = Z.L

structure GCS = Zippy_Goal_Clusters(Imperative_Union_Find)
structure GC = Zippy_Goal_Cluster(GCS)
structure F = Zippy_Focus(GCS)
structure T = Zippy_Tactic(Zippy_Tactic_Result(
  structure RD = Zippy_Result_Data
  structure RUD = Zippy_Result_Update_Data
  structure GPU = Zippy_GPos_Update_Util(
    structure F = F
    structure GPU = Zippy_GPos_Update(
      structure GCS = GCS
      structure T = Zippy_GPos_Update_Target))
  structure GC = GC))

structure Base =
struct
  structure AF = SArrow_Arrow_Apply.A
  structure AT = Kleisli_Arrow(AE.K.M)
  structure L = L
  fun lift f = AT.arr f
end

structure Z = Zippy_With_PAction(
  structure CO = CO
  structure Z = Zippy_With_PAction_Base(
    type copy_update_data = F.focus -> (GCS.cluster_pos * F.focus) list
    type prio = prio
    structure CD = Lift_Zippy_Copy_Data(open Base; structure CD = Zippy_Copy_Data)
    type @{T_args} cd_more = @{PolyT_arg 2}
    structure PAD = Lift_Zippy_PAction_Data(open Base; structure PAD = Zippy_PAction_Data)
    type @{T_args} pad_more = @{PolyT_arg 3}
    structure PD = Lift_Zippy_Prio_Data(open Base; structure PD = Zippy_Prio_Data)
    type @{T_args} pd_more = @{PolyT_arg 4}
    structure ZCORE = ZCORE
    structure Z = Z
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val zcore_content{i} = zcore_content{i}\<close>\<close>))

structure Z = Zippy_With_PResults(
  structure Z = Zippy_With_PResults_Base(
    type result = (rd_more T.result_data, T.update_data) T.RUD.result_update_data
    structure PRD = Lift_Zippy_PResults_Data(open Base; structure PRD = Zippy_PResults_Data)
    structure AND = Lift_Zippy_Actiona_Num_Data(open Base; structure AND = Zippy_Actiona_Num_Data)
    type @{T_args} action_and_more = @{PolyT_arg 3}
    type @{T_args} actiona_and_more = @{PolyT_arg 4}
    structure Z = Z))

structure Z = Zippy_With_Goals(
  structure Z = Zippy_With_Goals_Base(
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

structure Z = Gen_Zippy_Prover(Gen_Zippy_Prover_Base(
  structure GCS = GCS
  structure GC = GC
  structure F = F
  structure RDD = Lift_Zippy_Result_Data_Data(open Base; structure RDD = Zippy_Result_Data_Data)
  type @{T_args} rdd_more = @{PolyT_arg 4}
  structure T = T
  type rd_more = rd_more
  structure Z = Z))

structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} Z.ZCORE.N{i}.content\<close>\<close> end
structure ZCOREAZ1 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Content_Zipper"\<close>(
  open Base; structure Z = ZCOREAZ1)
structure ZCOREAZ2 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base; structure Z = ZCOREAZ2)
structure ZCOREAZ3 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base; structure Z = ZCOREAZ3)
structure ZCOREAZ4 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base; structure Z = ZCOREAZ4)
structure ZCOREAZ5 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
  open Base; structure Z = ZCOREAZ5)
open Z

end

functor Instantiate_Zippy_Prover_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER_BASE
  ) :
    ZIPPY_PROVER_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.zipper\<close>
      where start = 2\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
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
    where type @{T_args} gcsd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.gcsd_more
    where type @{T_args} gcd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.gcd_more
    where type @{T_args} cd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{T_args} action_fd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.action_fd_more
    where type @{T_args} rdd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.rdd_more
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{T_args} presults = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure ZCOREAZ1 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Content_Zipper"\<close>(open Base; structure Z = ZCOREAZ1)
structure ZCOREAZ2 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(open Base; structure Z = ZCOREAZ2)
structure ZCOREAZ3 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(open Base; structure Z = ZCOREAZ3)
structure ZCOREAZ4 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(open Base; structure Z = ZCOREAZ4)
structure ZCOREAZ5 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(open Base; structure Z = ZCOREAZ5)
structure Z = Instantiate_Gen_Zippy_Prover(open Base; structure Z = Z)
open Z
end

