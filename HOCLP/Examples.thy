\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Examples
  imports
    (* ML_Unification.ML_Logger *)
    (* ML_Unification.ML_Attributes *)
    (* ML_Unification.Setup_Result_Commands *)
    (* ML_Unification.ML_Term_Index *)
    (* ML_Unification.ML_Functor_Instances *)
    (* ML_Unification.ML_General_Utils *)
    (* ML_Unification.ML_Priorities *)
    (* Universal_Data.Universal_Data *)
    (* SpecCheck.SpecCheck_Show *)
    ML_Alternating_Bi_Zippers
    ML_Typeclasses.ML_State
begin

paragraph \<open>Summary\<close>
text \<open>A higher-order constraint logic programming tactic.\<close>

ML\<open>
  structure MO = Option_Monad_Or_Trans(Identity_Monad)
  structure ME = Monad_Exception_Monad_Or(MO)
  structure MS = State_Trans(structure M = ME; structure SR = Pair_State_Result_Base)
  structure MZ = IMonad_Zero_State_Trans(structure M = MO; structure S = MS)
  structure ME = IMonad_Exception_State_Trans(structure M = ME; structure S = MS)
  structure M = struct
    open MS; structure IM = IMonad_State(MS); open IM;
    open MZ; open ME; structure IM = IMonad(ME); open IM
  end
  structure MB = Move_Base(IKleisli(M))
\<close>

ML_file\<open>example_zippers.ML\<close>

ML\<open>
  local
  structure Int_Bi_Enum = Bi_Enumerable_Enumerable(
    type ('i, 'a, 'b) content = unit; structure E = Int_Enumerable(MB))
  val init_data = 0
  structure A = IArrow(IKleisli_IArrow_Apply(Int_Bi_Enum.First.K.M))
  fun init_data_move x = A.K init_data x
  structure Int_Bi_Zipper = Bi_Zipper_Bi_Enumerable(
    structure L = Example_Zippers.List
    structure E = Int_Bi_Enum
    fun unzip xs = L.foldl K xs init_data
    val init_data = init_data_move
  )
  in
  structure IAZ = Alternating_Bi_Zippers_Bi_Nodes(
    structure A = Alternating_Bi_Zippers_Bi_Nodes_Base_Args_Bi_Zippers(
      structure Z1 = Int_Bi_Zipper
      structure Z2 = Int_Bi_Zipper
      type ('i, 'c, 'n) ncontent1 = ('i, 'c, 'n) Z1.content
      type ('i, 'c, 'n) ncontent2 = ('i, 'c, 'n) Z2.content
      structure AC = Alternating_Bi_Containers(
        type ('i, 'c, 'n) container1 = ('i, 'c, 'n) Z1.container
        type ('i, 'c, 'n) container2 = ('i, 'c, 'n) Z2.container
      )
      val ncontent1 = I
      val ncontent2 = I
      val next1 = init_data_move
      val next2 = init_data_move
      val content1 = K
      val content2 = K
    )
    open A
    structure ZD  = Zipper_Data
    structure PM1 = M
    structure PM2 = M
  )
  end
  val _ = M.bind (M.bind (M.bind (IAZ.Z1.Init.move (0, M.throw ()))
    IAZ.Z1.Down.move)
    IAZ.Down1.move)
    IAZ.Up2.move
    |> (fn m => m "state")
    |> @{print}
\<close>

ML\<open>
  structure AZ = Alternating_Bi_Zippers_Bi_Nodes(
    structure A = Alternating_Bi_Zippers_Bi_Nodes_Base_Args_Simple_Zippers(
      type ('i, 'c, 'n) ncontent1 = 'c
      type ('i, 'c, 'n) ncontent2 = 'c
      structure Z1 = Example_Zippers.Rose_Zipper
      structure Z2 = Example_Zippers.Rose_Zipper
    )
    open A
    structure ZD  = Zipper_Data
    structure PM1 = M
    structure PM2 = M
  )
\<close>

ML\<open>
  structure E1 = DFS_Postorder_Enumerable_Bi_Zipper(structure ME = M; structure Z = AZ.Z1)
  structure E2 = DFS_Postorder_Enumerable_Bi_Zipper(structure ME = M; structure Z = AZ.Z2)
  structure T = Test(structure AZ = AZ; structure ME = M; structure E1 = E1; structure E2 = E2)
\<close>

ML\<open>
  local open AZ Example_Zippers M in
  fun mk_nodes _ =
    let
      val no_next = zero ()
      val no_children = Rose []
      val node0 = (N1.node 0 no_next, no_children)
      val node2 = (N1.node 2 no_next, Rose [(N1.node 1 no_next, no_children)])
      val node3 = (N1.node 3 no_next, Rose [node0, node2])
      val node7 = (N2.node 7 (Rose [node3] |> pure), no_children)
      val node4 = (N1.node 4 no_next, no_children)
      val node5 = (N1.node 5 (Rose [node7] |> pure), Rose [node4])
    in Rose [node5, node3] end
  end
\<close>

ML\<open>
  local
    structure AZP = Pair_Alternating_Bi_Zippers(structure AZ1 = AZ; structure AZ2 = IAZ)
    open AZP M
  in
  val test = (AZP.Z1.Init.move ((mk_nodes (), zero ()), (0, zero ()))
    >>= AZP.Z1.Right.move
    |> AZP.Z1.K.M.map (AZP.Z1.get_content #> fst #> AZ.N1.get_content))
    "state"
  end
\<close>

ML_val\<open>
  local
    structure MU = Move_Util(M); open AZ M
    fun content x = x |> (Z1.content () |> SLens.comp (N1.content ()) |> SLens.get)
    fun next x = x |> (Z1.content () |> SLens.comp (N1.next ()) |> SLens.get)
    fun f x acc =
      let
        val _ = @{print} (content x)
        (* val _ = @{print} (next x) *)
      in
        get ()
        >>= (fn state => put (state - 1))
        >>= (fn _ =>
        (if content x = 3 then MU.stop else MU.continue) (acc + 1)
        |> pure)
      end
  in
  (* val test = MU.AE.repeat ALNZ.Z2.Down.move  *)
  val test = (
    T.first1 (mk_nodes (), zero ())
    (* >>= (fn res => put "hello" *)
    (* >>= (fn _ => put 0 *)
    (* >>= (fn _ => pure res))) *)
    (* >>= T.next *)
    (* |> map_state (K "hooo") *)
    |> (fn x => MU.fold T.next f x 0)
    ) 0
    (* >>= AZ.Z1.Up.move *)
    (* >>= AZ.Down1.move *)
    (* >>= (fn zipper => (@{print} (AZ.Z2.get_content zipper); NONE)) *)
  (* val x = (E1.Init.move (nodes, NONE)) *)
    (* >>= ALNZ.Z1.Right.move *)
    (* >>= ALNZ.Z1.Up.move *)
    (* >>= ALNZ.Z1.Right.move *)
    (* >>= E1.Next.move
    >>= E1.Next.move
    >>= E1.Next.move
    >>= E1.Next.move *)
    (* >>= ALNZ.Z1.Down.move *)
    (* >>= ALNZ.Down1.move *)
    (* >>= ALNZ.Z2.Right.move *)
    (* >>= ALNZ.Up2.move *)
    (* |> the |> ALNZ.Z1.get_content *)
  end
\<close>

(* ML\<open>
  structure Util = HOCLP_Util
  @{functor_instance struct_name = HOCLPDT
    and functor_name = HOCLP
    and id = \<open>"dt"\<close>
    and more_args = \<open>structure TI = Discrimination_Tree\<close>}
  open HOCLPDT
\<close> *)

(* ML_file\<open>hoclp_tactic.ML\<close> *)

(* ML\<open>
  fun make_result_tac_tree path_zipper res_children =
    let
      val mk_res = get_path_zipper_zipper path_zipper |> get_zipper_content |> get_node_content
        |> get_tac_app_mkres
      val res = apply_make_tac_app_result mk_res path_zipper res_children
      val opt_res = move_up_path_tac_tree_zipper path_zipper
        |> Option.mapPartial move_up_path_tree_zipper
        |> Option.map (fn path_zipper => make_result_tac_tree path_zipper res)
    in the_default res opt_res end
  fun make_result_tree path_zipper =
    let
      val res = get_path_zipper_state path_zipper
      val opt_res = move_up_path_tree_zipper path_zipper
        |> Option.map (fn path_zipper => make_result_tac_tree path_zipper res)
    in the_default res opt_res end
\<close>

declare[[ML_print_depth=2000]]
ML\<open>
  let
    val tac = resolve_tac @{context} @{thms reflexive} 1 |> HOCLP_Tactic.leaf_tac_from_tactical
    val mk_tac_app_res = HOCLP_Tactic.mk_tac_app_res_from_tactical
    fun modify_prio t i = case t of
      {content = Goal_Cluster {state,...}, children} =>
      {content = Goal_Cluster {state = state, prio_tac_ret =
        prio_tac_ret (K (SOME (prio_content i tac)))},
        children = children}
    val t : (prio_tac_ret, mr) tree = tree [
      HOCLPDT.init_tree_node,
      case modify_prio HOCLPDT.init_tree_node 1 of
        {content = content,...} =>
        {content = content, children = tac_tree [
          {content = Tac_App {mkres = mk_tac_app_res}, children = ET.Tree [modify_prio HOCLPDT.init_tree_node 4]},
          {content = Tac_App {mkres = mk_tac_app_res}, children = ET.Tree [modify_prio HOCLPDT.init_tree_node 10]}
        ]},
      case modify_prio HOCLPDT.init_tree_node 2 of
        {content = content,...} =>
        {content = content, children = tac_tree [
          {content = Tac_App {mkres = mk_tac_app_res}, children = ET.Tree [modify_prio HOCLPDT.init_tree_node 4]}
        ]}
    ]
    val selection = select_tree_zipper t
    val res = Option.mapPartial apply_tac selection
  in
    res |> the
    |> move_down_path_tree_zipper |> the |> move_down_path_tac_tree_zipper |> the
    (* |> get_path_zipper_zipper |> get_zipper_content |> get_node_content *)
    |> make_result_tree
  end
\<close> *)

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
