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
    ML_Alternating_Bi_Zippers
    ML_Typeclasses.ML_State
begin

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
    structure AE = IArrow_Exception(IKleisli_Arrow_Exception(M))
    structure AAC = IKleisli_IArrow_Apply_Choice(M)
    structure AA = struct structure AA = AAC structure A = IArrow(AA) end
    structure MB = Move_Base(AA.A)
    end
  end
\<close>

ML_file\<open>example_zippers.ML\<close>

ML\<open>
  structure GList = GList(SIn.M)
  (* structure Data_Zipper = Rose_Zipper( *)
  structure Data_Zipper = List_Zipper(
    (* structure Z = Rose_Zipper_Base(GList) *)
    (* structure AC = SIn.AAC *)
    structure Z = List_Zipper_Base(GList)
    fun mk_exn_horizontal _ = SIn.AA.A.K ()
  )
  structure AZ = Alternating_Bi_Zippers_Bi_Nodes(
    structure A = Alternating_Bi_Zippers_Bi_Nodes_Base_Args_Simple_Zippers(
      structure A1 = SIn.AA.A
      structure A2 = SIn.AA.A
      type ('i, 'c, 'n) ncontent1 = 'c
      type ('i, 'c, 'n) ncontent2 = 'c
      structure Z1 = Data_Zipper
      structure Z2 = Data_Zipper
    )
    structure UA1 = SIn.AA
    structure UA2 = SIn.AA
    structure DA1 = SIn.AA
    structure DA2 = SIn.AA
    structure ZD  = Zipper_Data
  )
\<close>

ML\<open>
  structure E1 = DFS_Postorder_Enumerable_Bi_Zipper(structure AE = SIn.AE; structure Z = AZ.Z1)
  structure E2 = DFS_Postorder_Enumerable_Bi_Zipper(structure AE = SIn.AE; structure Z = AZ.Z2)
  structure T1 = Test(structure AZ = AZ; structure AE = SIn.AE; structure E1 = E1; structure E2 = E2)
  structure T2 = Test(structure AZ = Flip_Alternating_Bi_Zippers(AZ); structure AE = SIn.AE;
    structure E1' = E1; structure E1 = E2; structure E2 = E1')
\<close>

lemma sillyrule: "PROP Q \<Longrightarrow> PROP P" sorry

ML_file\<open>util.ML\<close>
ML_file\<open>coroutine.ML\<close>

ML_file\<open>mk_action.ML\<close>

ML\<open>
fun init_nodes content next =
  let val node = AZ.N1.node content next
  in GList.cons node GList.empty end
  (* in Data_Zipper.rose (GList.cons (node, Data_Zipper.rose GList.empty) GList.empty) end *)
fun init_nodes_no_next content = init_nodes content SIn.AE.throw
\<close>

ML\<open>
  structure Mk_Action = Mk_Action(
    structure A = SIn.AA.A
    type ('i, 'a, 'b, 'ma) zipperma = ('i, ('a, 'ma) Content_Mk_Action.cma, 'b) AZ.Z2.zipper
  )
\<close>

ML\<open>
  local open SIn.M in
  val tac = resolve0_tac [@{thm sillyrule}] |> SOMEGOAL
  val coroutine = Mk_Action.Coroutine.coroutine (fn zipper =>
    let
      val prio = 0
      val act = pure
      val next = Mk_Action.Coroutine.coroutine (fn _ => throw ())
    in ((prio, act), next) |> pure end)
  end
\<close>

ML\<open>
  (* fun init_action_content _ = *)
    (* (fn g => fn _ => (resolve0_tac [@{thm sillyrule}] |> SOMEGOAL) g |> M.pure) *)
    (* |> HOCLP.with_parent_content *)
    (* |> HOCLP.mk_action_content_seq Prio.MEDIUM *)
\<close>

ML\<open>
  local structure MU = Move_Util(structure AE = SIn.AE; structure AC = SIn.AAC) open MU.SC SIn.AA.A in
  val init_parent = SIn.AE.throw
  val init_content = Goal.init @{cprop "PROP P"}
  (* val init_action_content = CMA.mk_content "blub" (init_action_content ()) *)
  val init_action_content = 0
  fun mk_init_nodes _ =
    init_nodes init_content (SIn.AA.A.K [AZ.N2.node init_action_content SIn.AE.throw])

  (* local open AZ Data_Zipper in
  fun mk_init_nodes _ =
    let
      val no_next = SIn.AE.throw
      fun no_children _ = rose []
      val Knext = SIn.AA.A.K
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
  val update = arr (tap (fst #> AZ.Z1.get_content #> @{print})
    #> snd
    #> MU.AF.continue)

  (* fun run_action mact = catch *)
    (* (mact >>= (fn (p, act) => (@{print} "action!"; act))) *)
    (* (fn exn => (@{print} "no further action"; throw exn)) *)

  val test =  (mk_init_nodes (), init_parent)
    |> (T1.first1 ()
      (* >>> AZ.Down1.move () *)
      >>> arr (rpair 0)
      >>> MU.AF.fold (T1.next ()) update
    )
    (* |> (fn x => MU.fold T2.next update x (zero ())) >>= run_action) *)
    (* |> funpow 2 (fn x => SIn.M.bind (SIn.M.map AZ.Z2.unzip x) (T2.first1 ())) *)
    |> (fn st => st @{context})
    (* |> @{print} *)
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
