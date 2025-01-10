\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover
  imports
    ML_Union_Find
    ML_Unification.Unify_Resolve_Tactics_Base
    ML_Zipper4_Instances
    Zippy_Goals
begin

paragraph \<open>Summary\<close>
text \<open>Theorem proving framework based on zipper data structures.\<close>

ML_file\<open>zippy_thm_state.ML\<close>
ML_file\<open>zippy_goal_clusters.ML\<close>
ML_file\<open>zippy_goal_cluster.ML\<close>
ML_file\<open>zippy_focus.ML\<close>

ML_file\<open>zippy_action_num_data.ML\<close>

ML_file\<open>zippy_prover_base.ML\<close>

ML_file\<open>zippy_goal_pos_update.ML\<close>
ML_file\<open>zippy_goal_pos_update_util.ML\<close>

ML_file\<open>zippy_result_update_data.ML\<close>
ML_file\<open>zippy_tactic_result.ML\<close>
ML_file\<open>zippy_tactic.ML\<close>

ML_file\<open>zippy_prover_base_util.ML\<close>

ML_file\<open>zippy_prover_args.ML\<close>
ML_file\<open>zippy_prover.ML\<close>

paragraph \<open>The standard Zippy instance\<close>

ML\<open>
local
  structure MO = Option_Monad_Or_Trans(Identity_Monad)
  structure ME = Monad_Exception_Monad_Or(MO)
  structure MS = State_Trans(structure M = ME; structure SR = Pair_State_Result_Base)
  structure M = IMonad_Exception_State_Trans(structure M = ME; structure S = MS)
  structure M : MONAD_EXCEPTION_BASE = struct open M type ('p1, 'a) t = (unit, 'p1, 'p1, 'a) t end
  structure LZ = List_Zipper4(
    structure A = Kleisli_Arrow(M)
    structure L = Lens(structure A = A; structure L = Lens_Base(Kleisli_Arrow_Apply(M)))
    structure LI = GList(M)
    fun mk_exn_horizontal x = x |> A.K ()
  )
  structure AE = Kleisli_Arrow_Exception_Rec(Kleisli_Arrow_Exception(M))
  @{functor_instance struct_name = ZPA
    and functor_name = Zippy_Prover_Args
    and id = \<open>""\<close>
    and more_args = \<open>
      structure LZ = LZ
      val parent_logger = zippy_logger\<close>
    }
in
  structure Zippy = Zippy_Prover(ZPA)
  structure AE = AE
  structure Zippy_Monad = M
  structure Zippy_DFS4 = DFS_Postorder_Enumerable_Alternating_Zippers4(
    structure Base = struct structure AE = AE end
    structure AZ = Rotate_Alternating_Zippers4(Rotate_Alternating_Zippers4(Rotate_Alternating_Zippers4(Zippy)))
    structure E1 = DFS_Postorder_Enumerable4_Zipper_Moves(open Base; structure Z = AZ.Z1.ZM)
    structure E2 = DFS_Postorder_Enumerable4_Zipper_Moves(open Base; structure Z = AZ.Z2.ZM)
    structure E3 = DFS_Postorder_Enumerable4_Zipper_Moves(open Base; structure Z = AZ.Z3.ZM)
    structure E4 = DFS_Postorder_Enumerable4_Zipper_Moves(open Base; structure Z = AZ.Z4.ZM)
    structure AE = AE
  )
end
\<close>

lemma test: "PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP G \<Longrightarrow> PROP B \<Longrightarrow> (PROP A \<Longrightarrow> PROP A) \<Longrightarrow> PROP E \<Longrightarrow> PROP A &&& PROP B &&& PROP C &&& PROP D &&& PROP E &&& PROP F &&& PROP G"
  sorry

lemma cheat: "PROP P"
  sorry

ML\<open>
  structure AF = Kleisli_Arrow_Fold_Exception_Rec(AE)
  fun min_ord ord (x, y) = if is_less_equal (ord (x, y)) then x else y
  fun max_ord ord (x, y) = if is_greater_equal (ord (x, y)) then x else y

  fun eq_ord _ = EQUAL
  fun fst_ord ord = prod_ord ord eq_ord
\<close>

ML\<open>

  local structure Z = Zippy structure SC = Semi_Category(Z)
    structure A = Kleisli_Arrow_Arrow_Apply(Zippy_Monad)
    open SC A.A
  in
    val init_state = @{thm test} |> Goal.protect 6
    val halve_prio_co = Z.Kupdate_prio_co (fn x => x / 2.0)
    val cheat_tac = resolve0_tac [@{thm cheat}]
      |> Z.T.lift_all_goals_focus_tac
    fun presults_from_tac p f (x : (Proof.context, real, Z.TR.result_update_data) Z.pzipper2) :
    (Proof.context, (Proof.context, real, Z.TR.result_update_data) Z.ppresults) Zippy_Monad.t =
      Z.presults_from_tac (halve_prio_co p) (cheat_tac f) x

    fun max x = max_ord (fst_ord (fst_ord Real.compare)) x
    val fold_get = Z.get_run_paction &&& id ()
    val fold = AF.fold_init Zippy_DFS4.next
      (AE.catch' (first fold_get >>> arr max) (arr snd) >>> arr AF.continue)
      (fold_get >>> arr AF.continue)
      >>> arr AF.dest_res
    fun pick (x : (Proof.context, real, Z.TR.result_update_data) Z.pzipper1) = x
      |> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS4.first2 >>> fold)
    fun step (x : (Proof.context, real, Z.TR.result_update_data) Z.pzipper1) = x |>
      (pick >>> A.AA.uncurry Z.run_action)
    fun up (x : (Proof.context, real, Z.TR.result_update_data) Z.pzipper4) = x |>
      (AE.repeat (Z.Up4.move >>> Z.Up3.move >>> Z.Up2.move >>> Z.Up1.move)
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Up2.move)
  end
\<close>

ML\<open>
   local structure Z = Zippy structure SC = Semi_Category(Z)
    structure A = Kleisli_Arrow_Arrow_Apply(Zippy_Monad)
    open SC A.A
  in
    val test =
      (Z.init_state
      >>> arr snd
      >>> Z.Down1.move
      >>> Z.add_presults_action (presults_from_tac 10.0) (Z.F.None)
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Z2.ZM.Down.move
      >>> Z.add_presults_action (presults_from_tac 10.0) (Z.F.None)
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Z2.ZM.Down.move
      >>> Z.add_presults_action (presults_from_tac 10.0) (Z.F.None)
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Z2.ZM.Down.move
      >>> Z.add_presults_action (presults_from_tac 10.0) (Z.F.None)
      >>> up >>> step
      >>> up >>> step
      >>> up >>> step
      >>> up >>> step >>> up
      >>> Z.finish_gclusters' @{context}
      >>> arr Seq.list_of
      (* >>> up >>> step
      >>> up >>> step
      >>> up >>> step
      >>> up >>> step *)
      (* >>> Z.Down4.move *)
      (* >>> Z.is_gcs_finished *)
      (* >>> Z.Down4.move *)
      (* >>> step >>> up *)
      (* >>> step >>> up *)

      )
      |> (fn f => f init_state @{context})
      |> the |> fst
      (* |> @{print} *)
      (* |> (fn f => f @{context}) *)
  end
\<close>

end
