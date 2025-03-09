\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Prover_Instances
  imports
    ML_Typeclasses.ML_State
    ML_Unification.ML_Priorities
    Zippy_Prover_Action_Metadata
    Zippy_Prover_Action_Cluster_Metadata
    Zippy_Prover_Metadata_Data
    Zippy_Prover_Position
    Zippy_Prover_Result_Metadata
begin

(*TODO: ordering including prios and non-closed subgoals*)
paragraph \<open>Summary\<close>
text \<open>The standard Zippy prover instance, using a state monad.\<close>

ML_file\<open>zippy_prover_instance_base.ML\<close>
ML_file\<open>zippy_prover_instance.ML\<close>

lemma cheat: "PROP P" sorry

ML_file\<open>zippy.ML\<close>


ML\<open>
  (* fun test x y z a b = Zippy.mk_actiona_node x y z a b  |> Zippy.MS.eval @{context} |> the *)
  fun test x y z a b = Zippy.mk_actiona_node x y z a b
\<close>

thm reflexive

ML\<open>
  val a = test
\<close>

(* structure Zippy_DFS = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable_Alternating_Zippers"\<close>(
  structure Base = struct structure AE = AE end
  structure Z = Rotate_Alternating_Zippers5(Rotate_Alternating_Zippers5(Rotate_Alternating_Zippers5(ZP)))
  structure E1 = DFS_Postorder_Enumerable5_Zipper_Moves(open Base; structure Z = Z.Z1.ZM)
  structure E2 = DFS_Postorder_Enumerable5_Zipper_Moves(open Base; structure Z = Z.Z2.ZM)
  structure E3 = DFS_Postorder_Enumerable5_Zipper_Moves(open Base; structure Z = Z.Z3.ZM)
  structure E4 = DFS_Postorder_Enumerable5_Zipper_Moves(open Base; structure Z = Z.Z4.ZM)
  structure E5 = DFS_Postorder_Enumerable5_Zipper_Moves(open Base; structure Z = Z.Z5.ZM)
  structure AE = AE) *)
(*
lemma test: "PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP G \<Longrightarrow> PROP B \<Longrightarrow> (PROP A \<Longrightarrow> PROP A) \<Longrightarrow> PROP E \<Longrightarrow> PROP A &&& PROP B &&& PROP C &&& PROP D &&& PROP E &&& PROP F &&& PROP G" sorry

lemma test2: "(PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP C \<Longrightarrow> PROP A &&& PROP B &&& PROP C" sorry

consts A :: "prop"
consts B :: "prop"
consts G :: "prop"
consts E :: "prop"
consts C :: "prop"
consts D :: "prop"
consts F :: "prop"
lemmas test_inst = test[of "PROP A" "PROP B" "PROP G" "PROP E" "PROP C" "PROP D" "PROP F"]
lemmas test_inst2 = test2[of "PROP A" "PROP B" "PROP C"]

(* lemma "A \<equiv> B \<Longrightarrow> A \<equiv> C" *)
  (* apply simp *)

ML\<open>
  local structure Z = Zippy; structure SC = Semi_Category(Z); structure C = Category(Z); open SC AE
  in
    val presults_from_tac = presults_from_tac @{context}
    val test =
      (Z.init_state (arr (rpair (Z.no_parent ()) #> rpair ((), Z.no_parent ()) #> rpair 0)) gcsd_more gsd_more
      >>> arr snd
      >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z1.zipper) => x)
      >>> Z.Down1.move
      >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z2.zipper) => x)
      >>> add_tac
      >>> Z.Up4.move >>> Z.Up3.move
      >>> cons_move_single_presults_action "ac2" "a2" (presults_from_tac Prio.MEDIUM) (Z.F.single 2)
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Z2.ZM.Down.move
      >>> cons_move_single_presults_action "ac3" "a3" (presults_from_tac Prio.LOW) Z.F.None
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Z2.ZM.Down.move
      >>> cons_move_single_presults_action "ac4" "a4" (presults_from_tac Prio.VERY_HIGH) Z.F.None
      >>> Z.Up4.move >>> Z.Up3.move >>> Z.Z2.ZM.Down.move
      >>> cons_move_single_presults_action "ac5" "a5" (presults_from_tac Prio.VERY_LOW) Z.F.None
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_run_max_paction >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z4.zipper) => x)
      (* >>> up >>> (Z.Z1.ZM.Unzip.move >>> Zippy_DFS.first3) >>> fold_max_paction >>> arr Z.AF.dest_res *)
      >>> up
      >>> arr (fn (x : (Proof.context, unit, unit, string, string, unit) Z.Z1.zipper) => x)
      >>> Z.Down1.move
      >>> Z.Down2.move
      >>> Z.Down3.move
      >>> Z.Down4.move
      (* >>> Z.Down5.move *)
      >>> Z.L.get (Z.L.lens_snd (Z.L.id ()))
      (* >>> Z.finish_gclusters_oldest_first @{context} *)
      )
      |> (fn f => f (@{thm test} |> Goal.protect 6) @{context})
      |> the |> fst
      (* |> Seq.list_of |> length *)
      (* |> (fn f => f @{context}) *)
  end
\<close>
*)
end
