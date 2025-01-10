\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Higher-Order Constraint Logic Programming (HOCLP)\<close>
theory HOCLP
  imports
    ML_Unification.ML_Attributes
    ML_Unification.ML_Priorities
    ML_Unification.ML_Tactic_Utils
    ML_Unification.ML_Term_Utils
    ML_Unification.ML_Term_Index
    ML_Unification.Unify_Resolve_Tactics_Base
    (* Universal_Data.Universal_Data *)
    SpecCheck.SpecCheck_Show
    ML_Typeclasses.ML_State
    ML_Alternating_Zippers4
    Zippy
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

ML\<open>
  structure SIn =
  struct
    local
    structure MO = Option_Monad_Or_Trans(Identity_Monad)
    structure ME = Monad_Exception_Monad_Or(MO)
    in
    structure MS = State_Trans(structure M = ME; structure SR = Pair_State_Result_Base)
    structure M = IMonad_Exception_State_Trans(structure M = ME; structure S = MS)
    structure M : MONAD_EXCEPTION_BASE = struct open M type ('p1, 'a) t = (unit, 'p1, 'p1, 'a) t end
    structure A =
    struct
      structure AE : KLEISLI_ARROW_EXCEPTION_REC = Kleisli_Arrow_Exception_Rec(
      struct
        structure AE = Kleisli_Arrow_Exception_Base(M); open AE
        structure A = Arrow_Exception(AE); open A
      end)
      (* structure AC = Kleisli_Arrow_Apply_Choice_Base(M) *)
      structure AA : KLEISLI_ARROW_ARROW_APPLY =
      struct
        structure AA = Kleisli_Arrow_Apply_Base(M); open AA
        structure AA = Arrow_Apply(AA); open AA
        structure A = Arrow(AA); open A
      end
      structure C = Category(AA.A)
      structure A : KLEISLI_ARROW = struct open AA AA.A end
      structure LE = Lens(structure A = A; structure L = Lens_Base(AA.AA))
    end
    structure GList = GList(M)
    structure MB = Move_Base(M)
    end
  end
\<close>

ML_file\<open>example_zippers.ML\<close>

ML\<open>
  structure Data_Zipper = List_Zipper(
    structure A = SIn.A.A
    structure L = SIn.A.LE
    structure LI = SIn.GList
    fun mk_exn_horizontal x = x |> SIn.A.A.K ()
  )
  structure AZ = Alternating_Zippers4_Nodes(
    structure A = Alternating_Zippers4_Nodes_Base_Args_Simple_Zippers(
      structure A = SIn.A.A
      type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1 = 'a1
      type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2 = 'a2
      type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3 = 'a3
      type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4 = 'a4
      structure Z1 = Data_Zipper
      structure Z2 = Data_Zipper
      structure Z3 = Data_Zipper
      structure Z4 = Data_Zipper
    )
    structure AA = SIn.A.AA
    structure ZD  = Zipper_Data
  )
\<close>

ML_file\<open>util.ML\<close>

ML_file\<open>content_mk_action.ML\<close>

ML_file\<open>Zippy/result_update_info.ML\<close>

lemma test: "A \<Longrightarrow> B \<Longrightarrow> G \<Longrightarrow> B \<Longrightarrow> (A \<Longrightarrow> A) \<Longrightarrow> E \<Longrightarrow> A &&& B &&& C &&& D &&& E &&& F &&& G"
  sorry

ML\<open>
datatype 'i pos_update_info = Skip | Move of 'i

datatype ('r, 'ui) result = Result of {
    result : 'r,
    update_info : 'ui
  }
\<close>

ML\<open>
datatype 'i pos_update_info = Skip | Move of 'i
datatype ('i, 'r) result = Result of {
    result : 'r,
    pos_update_info : 'i -> 'i pos_update_info
  }

val state = @{thm test} |> `Thm.nprems_of |> uncurry Goal.protect
val gclusterss = GCS.init state
val gclusters = GC.init (apsnd (map snd) gclusterss)

val DETERM_SUCCEED = the oo SINGLE
val cheat = Skip_Proof.cheat_tac @{context} |> ALLGOALS |> DETERM_SUCCEED

val solved_gclusterss = map (GC.get_state #> cheat #> GCS.init) gclusters
val solved_gclusters = solved_gclusterss |> map (apsnd (map snd) #> GC.init)

val finisheds = map (fst #> GCS.is_finished) solved_gclusterss
val test = GCS.finish_gclusters @{context} (map fst solved_gclusterss) (fst gclusterss)

(* val update = fold_index (fn (i, j) => General_Util.fun_update (equal j) i) indices (K (~1,~1)) *)
(* val test = GCS.mk_gpos_index (gclusterss |> snd |> map fst) *)
\<close>

ML_file\<open>hoclp.ML\<close>

lemma sillyrule: "PROP Q \<Longrightarrow> PROP P" sorry

ML\<open>
  val tac = resolve0_tac [@{thm sillyrule}] |> HEADGOAL
\<close>

ML\<open>
  local structure LE = SIn.LA.LE; structure MU = Move_Util(open SIn.LA) open MU.SC MU MU.A HOCLP in
  val defstate = ()
  fun eval_safe f x = f () x |> SIn.MS.eval defstate |> the
  fun mk_init_nodes _ =
    let
      val n4 = eval_safe AZ.N4.node (eval_safe CMA.content_mk_action (0, mk_action 1), AE.throw)
      fun datasq _ = Seq.cons @{thm refl} (Seq.single @{thm trans})
      (* fun datasq _ = Seq.make (fn _ => SOME (@{thm refl}, datasq ())) *)
      fun prioc prio = CO.coroutine (fn x =>
        x |> (first (K prio) >>> arr (rpair (prioc (Prio.halve prio)))))
      val ac = MAU.ac_from_sq (CO.throw ()) (prioc Prio.HIGH) (K (datasq ())) |> Ac
      val n3 = eval_safe AZ.N3.node (ac, K [n4])
      val n2 = eval_safe AZ.N2.node (Goal.init @{cprop "PROP P"}, K [n3])
      val n1 = eval_safe AZ.N1.node (Goal.init @{cprop "PROP P"}, K [n2])
    in [n1] end

  fun run_mk_action _ =
    (AZ.Z4.ZO.content () |> LE.comp (AZ.N4.content ()) |> LE.comp (CMA.mk_action ()) |> LE.get) &&& id ()
    >>> arr (fn (mk_action, x) => ((MA.run mk_action, x), x))
    >>> first AA.app
    |> Lazy_Cat_Util.unlift
  val ord = HOCLP_Util.fst_ord (HOCLP_Util.fst_ord Prio.ord)
  val max = HOCLP_Util.max_ord ord

  fun update _ = first run_mk_action
    >>> arr (Library.uncurry max)
    >>> arr MU.AF.continue
    |> Lazy_Cat_Util.unlift

  fun run_mk_action_res _ = first (arr snd) >>> AA.app
    |> Lazy_Cat_Util.unlift

  fun init _ = T4.first2
    |> Lazy_Cat_Util.unlift
  fun up _ = AE.repeat (AZ.Up2.move o AZ.Up3.move o AZ.Up4.move o AZ.Up1.move)
    |> Lazy_Cat_Util.unlift
  (* val next = AE.catch' T2.next (AZ.Up2.move >>> up >>> E1.Next.move >>> first2) *)

  fun unzip _ = AZ.Up4.move >>> AZ.Up3.move >>> AZ.Up2.move >>> up >>> AZ.Z1.ZM.Unzip.move
    |> Lazy_Cat_Util.unlift
  fun step _ = init
    >>> arr (fn (x : (unit, Prio.prio, thm, thm, thm, int, int) zipper4) => x)
    >>> MU.AF.fold_init T4.next update (run_mk_action >>> arr MU.AF.continue)
    >>> arr MU.AF.dest_res
    >>> run_mk_action_res
    >>> unzip
    |> Lazy_Cat_Util.unlift
  fun result n =
    (
      (* step *)
      C.repeatn n step
      (* >>> AZ.Z1.Init.move *)
      (* >>> step *)
      |> Lazy_Cat_Util.unlift
    ) (mk_init_nodes (), AE.throw)
  end
\<close>

ML\<open>
  val a = result 0
    |> SIn.MS.eval ()
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

declare[[ML_dattr "fn _ => Logger.set_log_levels zippy_logger Logger.ALL"]]
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
