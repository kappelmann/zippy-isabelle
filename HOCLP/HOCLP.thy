\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Higher-Order Constraint Logic Programming (HOCLP)\<close>
theory HOCLP
  imports
    ML_Unification.ML_Attributes
    ML_Unification.ML_Functor_Instances
    ML_Unification.ML_Logger
    ML_Unification.ML_Priorities
    ML_Unification.ML_Tactic_Utils
    ML_Unification.ML_Term_Utils
    ML_Unification.ML_Term_Index
    (* ML_Unification.ML_General_Utils *)
    ML_Unification.Setup_Result_Commands
    (* Universal_Data.Universal_Data *)
    SpecCheck.SpecCheck_Show
    ML_Alternating_QZippers
    ML_Typeclasses.ML_State
    Main
begin

(*
Arrows:
https://www.sciencedirect.com/science/article/pii/S0167642399000234?ref=pdf_download&fr=RR-2&rr=8da1f2486fc3bbb0
Arrow Loop:
https://www.staff.city.ac.uk/~ross/papers/notation.pdf
*)

paragraph \<open>Summary\<close>
text \<open>A higher-order constraint logic programming tactic.\<close>

setup_result hoclp_logger = \<open>Logger.new_logger Logger.root "HOCLP"\<close>

ML\<open>
  structure SIn =
  struct
    local
    structure MO = Option_Monad_Or_Trans(Identity_Monad)
    structure ME = Monad_Exception_Monad_Or(MO)
    structure MS = State_Trans(structure M = ME; structure SR = Pair_State_Result_Base)
    in
    structure M = IMonad_Exception_State_Trans(structure M = ME; structure S = MS)
    structure A =
    struct
      structure L : ILAZY_COMP = IKleisli_Arrow_Apply_Choice(M)
      structure AE = IArrow_Exception_Rec(
        structure A = IArrow_Exception(IKleisli_Arrow_Exception(M))
        structure L = L
      )
      structure AA = IKleisli_Arrow_Apply_Choice(M)
      structure AC = AA
      structure C = ICategory(AA)
      structure A = IArrow(AC)
    end
    structure LA =
    struct
      structure L = Lazy_Lazy_Comp(A.L)
      structure AE = Lazy_IArrow_Exception_Rec(A.AE)
      structure AA = Lazy_IArrow_Apply_Base(A.AA)
      structure AC = IArrow_Choice(Lazy_IArrow_Choice_Base(A.AC))
      structure C = Lazy_ICategory(A.C)
      structure A = Lazy_IArrow(A.A)
    end
    structure MB = Move_Base(LA.A)
    end
  end
\<close>

ML_file\<open>example_zippers.ML\<close>

ML\<open>
  structure GList = GList(SIn.M)
  (* structure Data_Zipper = Rose_Zipper( *)
  structure Data_Zipper = List_Zipper(
    (* structure Z = Rose_Zipper_Base(GList) *)
    (* structure AC = IArrow_Choice(SIn.A.AC) *)
    structure Z = List_Zipper_Base(GList)
    fun mk_exn_horizontal _ = SIn.A.A.K ()
  )
  structure AZ = Alternating_QZippers_QNodes(
    structure A = Alternating_QZippers_QNodes_Base_Args_Simple_Zippers(
      structure A1 = SIn.LA.A
      structure A2 = SIn.LA.A
      structure A3 = SIn.LA.A
      structure A4 = SIn.LA.A
      type ('i, 'a, 'b, 'c, 'd) ncontent1 = 'a
      type ('i, 'a, 'b, 'c, 'd) ncontent2 = 'a
      type ('i, 'a, 'b, 'c, 'd) ncontent3 = 'a
      type ('i, 'a, 'b, 'c, 'd) ncontent4 = 'a
      structure Z1 = Data_Zipper
      structure Z2 = Data_Zipper
      structure Z3 = Data_Zipper
      structure Z4 = Data_Zipper
    )
    structure DA1 = SIn.LA
    structure DA2 = SIn.LA
    structure DA3 = SIn.LA
    structure DA4 = SIn.LA
    structure UA1 = SIn.LA
    structure UA2 = SIn.LA
    structure UA3 = SIn.LA
    structure UA4 = SIn.LA
    structure ZD  = Zipper_Data
  )
\<close>

ML_file\<open>util.ML\<close>
ML_file\<open>coroutine.ML\<close>
ML_file\<open>mk_action.ML\<close>

ML\<open>
  structure CMA = Content_Mk_Action
  structure CO = ICoroutine_Util(
    structure CO = ICoroutine(SIn.LA.A)
    structure AE = SIn.LA.AE
  )
  structure MA = Mk_Action(
    structure M = SIn.MB
    type ('i, 'a, 'b, 'c, 'd, 'ma) data = ('i, ('a, 'ma) CMA.cma, 'b, 'c, 'd) AZ.Z4.zipper
  )
  structure MAU = Mk_Action_Util(
    open SIn.LA
    structure MA = MA
    structure CO = CO
  )
\<close>

lemma sillyrule: "PROP Q \<Longrightarrow> PROP P" sorry

ML\<open>
  val tac = resolve0_tac [@{thm sillyrule}] |> HEADGOAL
\<close>

ML\<open>
  (* ('a, 'b, int, 'c, 'd, ('a, 'c, 'b, int, 'c, 'd, 'e) MAU.pd_ac) MA.data *)
datatype ('p, 'x, 'i, 'a, 'b, 'c, 'd) mk_ac = Mk_AC of
  ('p, 'x, 'i, 'a, 'b, 'c, ('p, 'x, 'i, 'a, 'b, 'c, 'd) mk_ac) MAU.pd_ac
  ('i, 'i, ('p, 'i, 'a, 'b, 'c, 'd) MA.data, 'p, 'x) CO.acoroutine

type ('p, 'x, 'i, 'a, 'b, 'c, 'd) pz_ac = ('p, 'x, 'i, 'a, 'b, 'c, ('p, 'x, 'i, 'a, 'b, 'c, 'd) mk_ac) MAU.pd_ac
type ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper3 =
  ('i, ('p, 'x, 'i, 'b, 'c, 'd, 'a) mk_ac, 'b, 'c, 'd) AZ.Z3.zipper
type ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4 = ('p, 'i, 'a, 'b, 'c, ('p, 'x, 'i, 'a, 'b, 'c, 'd) mk_ac) MA.data
type ('p, 'x, 'i, 'a, 'b, 'c, 'd) node4 =
  ('i, ('a, ('p, 'i, 'a, 'b, 'c, ('p, 'x, 'i, 'a, 'b, 'c, 'd) mk_ac) MA.mk_action) CMA.cma, 'b, 'c, ('p, 'x, 'i, 'a, 'b, 'c, 'd) mk_ac) AZ.N4.node
(* type ('p, 'i, 'a, 'b, 'c, 'd) to = 'p * ('i, ('p, 'i, 'a, 'b, 'c, 'd) data) hom_move *)

fun mk_ac mkac = Mk_AC mkac
fun dest_mk_ac (Mk_AC mkac) = mkac
\<close>

(* ML\<open>
signature REC_QDATA =
sig
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data1
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data2
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data3
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data4

  type ('i, 'a, 'b, 'c, 'd) rdata1
  type ('i, 'a, 'b, 'c, 'd) rdata2
  type ('i, 'a, 'b, 'c, 'd) rdata3
  type ('i, 'a, 'b, 'c, 'd) rdata4

  val dest_rdata1 : ('i, 'a, 'b, 'c, 'd) rdata1 ->
    ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata1, ('i, 'b, 'c, 'd, 'a) rdata2,
    ('i, 'c, 'd, 'a, 'b) rdata3, ('i, 'd, 'a, 'b, 'c) rdata4) data1
  val rdata1 : ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata1, ('i, 'b, 'c, 'd, 'a) rdata2,
    ('i, 'c, 'd, 'a, 'b) rdata3, ('i, 'd, 'a, 'b, 'c) rdata4) data1 ->
    ('i, 'a, 'b, 'c, 'd) rdata1

  val dest_rdata2 : ('i, 'a, 'b, 'c, 'd) rdata2 ->
    ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata2, ('i, 'b, 'c, 'd, 'a) rdata3,
    ('i, 'c, 'd, 'a, 'b) rdata4, ('i, 'd, 'a, 'b, 'c) rdata1) data2
  val rdata2 : ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata2, ('i, 'b, 'c, 'd, 'a) rdata3,
    ('i, 'c, 'd, 'a, 'b) rdata4, ('i, 'd, 'a, 'b, 'c) rdata1) data2 ->
    ('i, 'a, 'b, 'c, 'd) rdata2

  val dest_rdata3 : ('i, 'a, 'b, 'c, 'd) rdata3 ->
    ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata3, ('i, 'b, 'c, 'd, 'a) rdata4,
    ('i, 'c, 'd, 'a, 'b) rdata1, ('i, 'd, 'a, 'b, 'c) rdata2) data3
  val rdata3 : ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata3, ('i, 'b, 'c, 'd, 'a) rdata4,
    ('i, 'c, 'd, 'a, 'b) rdata1, ('i, 'd, 'a, 'b, 'c) rdata2) data3 ->
    ('i, 'a, 'b, 'c, 'd) rdata3

  val dest_rdata4 : ('i, 'a, 'b, 'c, 'd) rdata4 ->
    ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata4, ('i, 'b, 'c, 'd, 'a) rdata1,
    ('i, 'c, 'd, 'a, 'b) rdata2, ('i, 'd, 'a, 'b, 'c) rdata3) data4
  val rdata4 : ('i, 'a, 'b, 'c, 'd, ('i, 'a, 'b, 'c, 'd) rdata4, ('i, 'b, 'c, 'd, 'a) rdata1,
    ('i, 'c, 'd, 'a, 'b) rdata2, ('i, 'd, 'a, 'b, 'c) rdata3) data4 ->
    ('i, 'a, 'b, 'c, 'd) rdata4
end

functor Rec_QData(
    type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data1
    type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data2
    type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data3
    type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data4
  ) : REC_QDATA =
struct

type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data1 = ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data1
type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data2 = ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data2
type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data3 = ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data3
type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data4 = ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data4

datatype ('i, 'a, 'b, 'c, 'd) rdata1 = RData1 of ('i, 'a, 'b, 'c, 'd,
  ('i, 'a, 'b, 'c, 'd) rdata1,
  ('i, 'b, 'c, 'd, 'a) rdata2,
  ('i, 'c, 'd, 'a, 'b) rdata3,
  ('i, 'd, 'a, 'b, 'c) rdata4) data1
and ('i, 'a, 'b, 'c, 'd) rdata2 = RData2 of ('i, 'a, 'b, 'c, 'd,
  ('i, 'a, 'b, 'c, 'd) rdata2,
  ('i, 'b, 'c, 'd, 'a) rdata3,
  ('i, 'c, 'd, 'a, 'b) rdata4,
  ('i, 'd, 'a, 'b, 'c) rdata1) data2
and ('i, 'a, 'b, 'c, 'd) rdata3 = RData3 of ('i, 'a, 'b, 'c, 'd,
  ('i, 'a, 'b, 'c, 'd) rdata3,
  ('i, 'b, 'c, 'd, 'a) rdata4,
  ('i, 'c, 'd, 'a, 'b) rdata1,
  ('i, 'd, 'a, 'b, 'c) rdata2) data3
and ('i, 'a, 'b, 'c, 'd) rdata4 = RData4 of ('i, 'a, 'b, 'c, 'd,
  ('i, 'a, 'b, 'c, 'd) rdata4,
  ('i, 'b, 'c, 'd, 'a) rdata1,
  ('i, 'c, 'd, 'a, 'b) rdata2,
  ('i, 'd, 'a, 'b, 'c) rdata3) data4

val rdata1 = RData1
fun dest_rdata1 (RData1 x) = x

val rdata2 = RData2
fun dest_rdata2 (RData2 x) = x

val rdata3 = RData3
fun dest_rdata3 (RData3 x) = x

val rdata4 = RData4
fun dest_rdata4 (RData4 x) = x
end

signature CONTENT_MK_ACTION =
sig
  type ('c, 'ma) cma
  val mk_content_mk_action: 'c -> 'ma -> ('c, 'ma) cma

  val get_content : ('c, 'ma) cma -> 'c
  val get_mk_action : ('c, 'ma) cma -> 'ma

  val map_content : ('c1 -> 'c2) -> ('c1, 'ma) cma -> ('c2, 'ma) cma
  val map_mk_action : ('ma1 -> 'ma2) -> ('c, 'ma1) cma -> ('c, 'ma2) cma

  val content : unit -> (('c2, 'ma) cma, 'c2, ('c1, 'ma) cma, 'c1) SLens.lens
  val mk_action : unit -> (('c, 'ma2) cma, 'ma2, ('c, 'ma1) cma, 'ma1) SLens.lens
end

structure Rec_Zippers = Rec_QData(
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data1 = ('i, 'a, 'b, 'c, 'd) AZ.Z1.zipper
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data2 = ('i, 'a, 'b, 'c, 'd) AZ.Z2.zipper
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data3 = ('i, 'a, 'b, 'c, 'd) AZ.Z3.zipper
  type ('i, 'a, 'b, 'c, 'd, 'r1, 'r2, 'r3, 'r4) data4 = ('i, 'a, 'b, 'c, 'd) AZ.Z4.zipper
)

structure AZN = AZ
structure AZ = Replace_Alternating_QZippers_Zipper(
  structure A1 = SIn.LA.A
  structure A2 = SIn.LA.A
  structure A3 = SIn.LA.A
  structure A4 = SIn.LA.A
  structure DA1 = SIn.LA.A
  structure DA2 = SIn.LA.A
  structure DA3 = SIn.LA.A
  structure DA4 = SIn.LA.A
  structure UA1 = SIn.LA.A
  structure UA2 = SIn.LA.A
  structure UA3 = SIn.LA.A
  structure UA4 = SIn.LA.A
  structure AZ = AZ
  type ('i, 'a, 'b, 'c, 'd) nzipper1 = ('i, 'a, 'b, 'c, 'd) Rec_Zippers.rdata1
  type ('i, 'a, 'b, 'c, 'd) nzipper2 = ('i, 'a, 'b, 'c, 'd) Rec_Zippers.rdata2
  type ('i, 'a, 'b, 'c, 'd) nzipper3 = ('i, 'a, 'b, 'c, 'd) Rec_Zippers.rdata3
  type ('i, 'a, 'b, 'c, 'd) nzipper4 = ('i, 'a, 'b, 'c, 'd) Rec_Zippers.rdata4
  val nzipper1 = Rec_Zippers.rdata1
  val nzipper2 = Rec_Zippers.rdata2
  val nzipper3 = Rec_Zippers.rdata3
  val nzipper4 = Rec_Zippers.rdata4
  val dest_nzipper1 = Rec_Zippers.dest_rdata1
  val dest_nzipper2 = Rec_Zippers.dest_rdata2
  val dest_nzipper3 = Rec_Zippers.dest_rdata3
  val dest_nzipper4 = Rec_Zippers.dest_rdata4
)
\<close> *)

ML\<open>
  structure E1 = DFS_Postorder_Enumerable_QZipper(structure AE = SIn.LA.AE; structure Z = AZ.Z1)
  structure E2 = DFS_Postorder_Enumerable_QZipper(structure AE = SIn.LA.AE; structure Z = AZ.Z2)
  structure E3 = DFS_Postorder_Enumerable_QZipper(structure AE = SIn.LA.AE; structure Z = AZ.Z3)
  structure E4 = DFS_Postorder_Enumerable_QZipper(structure AE = SIn.LA.AE; structure Z = AZ.Z4)
  structure T1 = Test(structure AZ = AZ; structure AE = SIn.LA.AE; structure L = SIn.LA.L;
    structure E1 = E1; structure E2 = E2; structure E3 = E3; structure E4 = E4)
  structure T2 = Test(structure AZ = Rotate_Alternating_QZippers(AZ); structure AE = SIn.LA.AE; structure L = SIn.LA.L;
    structure E1' = E1; structure E1 = E2; structure E2 = E3; structure E3 = E4; structure E4 = E1')
\<close>

ML\<open>
  local structure MU = Move_Util(open SIn.LA) open MU MU.SC MU.A in
  fun mk_prio_sq_c prio =
    arr (fn (_, sq) => ((prio, sq), mk_prio_sq_c (Prio.halve prio)))
    |> CO.coroutine
  fun ac_empty_sq _ = CO.throw ()
  fun ac_from_sq get_sq = MAU.ac_from_sq (ac_empty_sq ()) (mk_prio_sq_c Prio.HIGH) get_sq
  fun mk_child content
  :
    ('p, 'x, 'i, 'a, 'b, 'c, 'd) pz_ac * ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4 ->
    ('p, 'x, 'i, 'a, 'b, 'c, 'd) node4
    =
    let
      val get = AZ.Z4.content () |> SLens.comp (AZ.N4.content ()) |> SLens.comp (CMA.mk_action ())
        |> SLens.get
      fun mk_node_no_child mka = AZ.N4.node (CMA.mk_content_mk_action content mka) AE.throw
    in snd #> get #> mk_node_no_child end
  fun append_child (ch : ('p, 'x, 'i, 'a, 'b, 'c, 'd) node4)
    (zipper : ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4) : ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4 =
    let val map = AZ.Z4.zcontext () |> SLens.comp (AZ.lzcontext4 ()) |> SLens.modify
    in map (Data_Zipper.append_zcontext ch, zipper) end
  fun update_tail_ac _
    : ('i, 'i, ('p, 'x, 'i, 'a, 'b, 'c, 'd) pz_ac
      * ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4, ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4) SIn.A.AA.cat
  =
    (let
      val map = AZ.Z4.zcontext () |> SLens.comp (AZ.parent4 ()) |> SLens.modify
      val set = AZ.ZD.content () |> SLens.set
      fun map_parent4 ac parent4 = arr (pair parent4) >>> AA.app >>> arr (Library.curry set (mk_ac ac))
    in arr (apfst map_parent4 #> map) end) ()
  fun update_ac content
    : ('i, ('p, 'x, 'i, 'a, 'b, 'c, 'd) pz_ac * ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4,
      ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4) MAU.MA.move
      =
    MAU.update_ac (arr (mk_child content)) (arr (Library.uncurry append_child)) update_tail_ac
  val e = ()
  fun set_mk_action mk_action =
    let val set = AZ.Z4.content () |> SLens.comp (AZ.N4.content ()) |> SLens.comp (CMA.mk_action ())
      |> SLens.set
    in arr (Library.curry set mk_action) end
  fun disable_mk_aktion_update_ac content
    : ('i, ('p, 'x, 'i, 'a, 'b, 'c, 'd) pz_ac * ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4, ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4) MAU.MA.move
    =
    MAU.disable_mk_aktion_update_ac e set_mk_action (update_ac content)
  fun update_pulled _
    : ('i, 'i, 'b * ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4, ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4) SIn.A.AA.cat
      =
    (let
      fun init_nodes content next =
        let val node = AZ.N1.node content next
        in GList.cons node GList.empty end
      val set = AZ.Z4.content () |> SLens.comp (AZ.N4.next ()) |> SLens.set
    in
      first (arr (fn content => K (init_nodes content AE.throw)))
      >>> arr set
    end) ()
(* ('i, ('p, 'i, 'a, 'b, 'c, 'd) mk_ac, 'b, 'c, 'd) AZ.Z3.zipper *)
  fun update_data content _
    : ('i, ('b * ('p, 'x, 'i, 'a, 'b, 'c, 'd) pz_ac) * ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4, ('p, 'x, 'i, 'a, 'b, 'c, 'd) zipper4) MAU.MA.move
    = MAU.update_data update_pulled (disable_mk_aktion_update_ac content)
  val datasq = Seq.cons @{thm refl} (Seq.single @{thm trans})
  fun mk_action content = MAU.mk_action_from_ac (update_data content) (AE.throw' ())
  end
\<close>

(* ML\<open> *)
  fun init_nodes content next =
    let val node = AZ.N1.node content next
    in GList.cons node GList.empty end
    (* in Data_Zipper.rose (GList.cons (node, Data_Zipper.rose GList.empty) GList.empty) end *)
  fun init_nodes_no_next content = init_nodes content SIn.LA.AE.throw

  local structure MU = Move_Util(open SIn.LA) open MU.SC MU MU.A in
  fun mk_action _ = MA.mk_action (AE.throw' ())
  val init_content = Goal.init @{cprop "PROP P"}
  (* val init_action_content = CMA.mk_content "blub" (init_action_content ()) *)
  val init_action_content = CMA.mk_content_mk_action 0 (mk_action ())
  fun mk_init_nodes _ =
    init_nodes init_content (K [AZ.N2.node init_action_content AE.throw,
      AZ.N2.node (CMA.mk_content_mk_action 0 (mk_action ())) AE.throw])

  (* local open AZ Data_Zipper in
  fun mk_init_nodes _ =
    let
      val no_next = SIn.LA.AE.throw
      fun no_children _ = rose []
      val Knext = SIn.LA.A.K
      val node0 = (N1.node 0 no_next, no_children ())
      val node2 = (N1.node 2 no_next, rose [(N1.node 1 no_next, no_children ())])
      val node3 = (N1.node 3 no_next, rose [node0, node2])
      val node7 = (N2.node 7 (rose [node3] |> Knext), no_children ())
      val node4 = (N1.node 4 no_next, no_children ())
      val node5 = (N1.node 5 (rose [node7] |> Knext), rose [node4])
    in rose [node5, node3] end
  end *)

  (* fun combine f x y = ME.catch (x >>= (fn xin => ME.catch (y >>= f xin) (K x))) (K y) *)
  (* fun update zipper acc = combine (pure oo max_ord ZCA.action_ord) acc (ZCA.get_action zipper) *)
    (* |> MU.continue |> pure *)

  val run_mk_action =
    arr (AZ.Z2.get_content #> AZ.N2.get_content #> CMA.get_mk_action) &&& id ()
    >>> arr (fn (mk_action, x) => ((MA.dest_mk_action mk_action, x), x))
    >>> first AA.app
    (* in MA.dest_mk_action mk_action () zipper end *)

  val ord = HOCLP_Util.fst_ord (HOCLP_Util.fst_ord Prio.ord)
  val max = HOCLP_Util.max_ord ord

  val update = first run_mk_action
    >>> arr (tap @{print})
    >>> arr (Library.uncurry max)
    >>> arr MU.AF.continue

  val run_mk_action_res = first (arr snd) >>> AA.app

  (* val first2 = AZ.Down1.move >>> arr AZ.Z2.unzip >>> T2.first1 *)
  (* fun init _  = (E1.First.move >>> first2) () *)
  (* fun init _ = T1.first1 *)
  (* fun up _ : int = AE.repeat (AZ.Up2.move o AZ.Up3.move o AZ.Up4.move o AZ.Up1.move) () *)
  (* val next = AE.catch' T2.next (AZ.Up2.move >>> up >>> E1.Next.move >>> first2) *)

  (* val unzip = AZ.Up2.move >>> up >>> arr AZ.Z1.unzip *)
  (* val step =
    init
    >>> arr (fn x : (Proof.context, (int, (Prio.prio, Proof.context, int, Thm.thm) MA.mk_action) CMA.cma,
      Thm.thm) AZ.Z2.zipper
      => x)
    >>> MU.AF.fold_init T2.next update (run_mk_action >>> arr MU.AF.continue)
    >>> arr MU.AF.dest_res
    >>> run_mk_action_res
    >>> unzip *)
  val result = (mk_init_nodes (), AE.throw)
    |> (
      AZ.Z1.Init.move
      (* C.repeatn 2 step *)
      (* >>> AZ.Z1.Init.move *)
      (* >>> AZ.Down1.move *)
    ) ()
    |> (fn st => st @{context})
  end
\<close>


ML_file\<open>hoclp_rule.ML\<close>

ML\<open>
  @{functor_instance struct_name = HOCLP_Rules_Test
    and functor_name = HOCLP_Rules
    and id = \<open>"test"\<close>
    and more_args = \<open>
      structure TI = Discrimination_Tree
      type tac = unit
      fun eq_tac _ = true
      fun pretty_tac _ _ = Pretty.str "test"
      \<close>}
\<close>

ML\<open>
  HOCLP_Rules_Test.add_rule ([()],
    @{thm sillyrule}) (Context.the_generic_context ())
\<close>

(* method_setup hoclpdt = HOCLPDT.hoclp_method_parser "Higher-Order Constraint Logic Programming"

declare[[ML_dattr "fn _ => Logger.set_log_levels hoclp_logger Logger.ALL"]]
declare[[eta_contract=false]]

theorem test:
  assumes "k \<equiv> k"
  shows "\<lambda>x. f x \<equiv> (\<lambda>y. g ((\<lambda>z. z) y) c) (\<lambda>y. d y)"
  sorry

ML\<open>
  val parse_ml_pos = Scan.repeat Parse.embedded_ml |> Util.parse_position
  fun parse_attr update = parse_ml_pos >> update
  val parse = Args.add |-- parse_attr HOCLPDT.add_hoclp_rule_attr
    || Args.del |-- parse_attr HOCLPDT.delete_hoclp_rule_attr
    || parse_attr HOCLPDT.add_hoclp_rule_attr
  val _ = Attrib.setup @{binding hoclp} (Scan.lift parse) "HOCLP rule" |> Theory.setup
\<close>

ML\<open>
  val hoclptac = HOCLPDT.print_hoclp_tactic
\<close>

lemma abc [hoclp add]:
  shows "F \<equiv> L N"
  sorry




lemma "F \<equiv> L N"
  apply hoclpdt
  oops

declare abc[hoclp del]

lemma ab [hoclp add hoclptac hoclptac] :
  assumes "A \<equiv> B"
  and "C \<equiv> D E"
  shows "F \<equiv> L N"
  and "Z \<equiv> Y"
  sorry

declare ab[hoclp hoclptac hoclptac]

ML\<open>
  (* val context = HOCLPDT.add_print_hoclp_rule @{thm abc(1)} (Context.Proof @{context}) *)
  (* val context = HOCLPDT.add_print_hoclp_rule @{thm abc(1)} (Context.Proof @{context}) *)
  (* val context = HOCLPDT.remove_print_hoclp_rule @{thm abc(2)} (Context.Proof @{context}) *)
  (* val context = HOCLPDT.add_print_hoclp_rule @{thm abc(1)} context *)
  val context = (Context.Proof @{context})
  val {rules = a} = HOCLPDT.HOCLP_Rules_Data.get context
    |> HOCLPDT.dest_hoclp_rules
  val b = Discrimination_Tree.content a |> map @{print}
\<close> *)

(*
Meeting notes:
1. What's the "selling point"?
2. Automatic inference of priorities
*)

(*
Kevin's notes:
-1. When inserting implicit arguments, pass all bound variables to meta variables
0. Specify solvers for assumptions of a lemma
1. Priority of rules
  - maybe priorities based on shape useful with update whenever a meta variables is instantiated?
    -> mapping from meta variables to goals
2. Priority of assumptions
3. Use first-order unifier (in most or all cases?)
  - Specification of unification algorithm for rules?
4. Postponing zero-priority rules (e.g. subtype conditions, additional assumptions)
5. consolidate remaining assumptions for variables using unification hints
6. Problem: guessing when applying Dep_fun_typeI
  - Idea: Types by HOL as a safeguard
7. Problem: how to discharge typeclass assumptions
  - Idea: Typeclasses are always defined as functions too and as such,
    we can automatically create a backward rule from the type rule when appropriately tagged
  - Note: typeclasses are like "canonical terms of a given type"
8. Notation and rules for type classes and implicits, i.e. {}, [] parameters
  - add pre-run to insert missing arguments
  - annotations for type classes can be added with app_dep_type2
9. Store proved theorems for follow-up goals and pass as assumptions?
  - caching of types for subterms
  - caching of derived typeclasses;
  - problem: need to keep track of context and check for diffs
10. use bidirectional breadth-first search for subtyping
11. compare with Mizar approach
12. compare with Lean approach
  - type classes use caching and suspended nodes with notifier for new solutions
  - reduction is taken into consideration, e.g. `B (snd \<langle>a, b\<rangle>)` and `B b` match)
  - lean does prioritise based on structure of constraints, e.g. flex flex, rigid,
    choice, etc. rather than priority;
    however, their constraints are unique (except for choice constraints) and
    hence whenever a, e.g. flex-flex pair, arises, they safely may be postponed
    because there is no other choice on the current goal. In our case, however,
    there may be other rules to complete the current goal.
13. subsume transfer and autoref?
14. Problem: how to stop applying rules recursively to meta-variables, e.g. app_type
  to `?X : ?TX`?
    Solutions:
  a. priorities that are recalculated whenever meta-variable is instantiated
     problem: should be solved immediately if solvable by assumption
  b. create delay rules
  c. use matching instead of unification
15. elaborating t : {x : A} \<rightarrow> B will result in \<lambda>{x} \<rightarrow> t, where {x} binds an implicit
argument
  - cf https://arxiv.org/pdf/1609.09709.pdf


- Abstract Logic Programming language: see miller overview paper;
  based on sequent calculus proof theory whose proofs correspond to search strategies
- Tabling methods evaluate programs by maintaining tables of subgoals and their
  answers and by resolving repeated occurrences of subgoals against answers from the table.
- subordination: check whether one can safely remove some assumptions
- retrieval: check for assumptions and goal or only check for goal and solve assumptions
- visiting the same goal twice without an answer -> fail
*)


end
