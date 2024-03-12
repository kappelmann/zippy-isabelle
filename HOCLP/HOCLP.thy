\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Higher-Order Constraint Logic Programming (HOCLP)\<close>
theory HOCLP
  imports
    ML_Unification.ML_Logger
    ML_Unification.ML_Attributes
    ML_Unification.Setup_Result_Commands
    ML_Unification.ML_Term_Index
    ML_Unification.ML_Functor_Instances
    ML_Unification.ML_General_Utils
    ML_Unification.ML_Priorities
    (* Universal_Data.Universal_Data *)
    SpecCheck.SpecCheck_Show
    ML_Zippers
begin

paragraph \<open>Summary\<close>
text \<open>A higher-order constraint logic programming tactic.\<close>

setup_result hoclp_logger = \<open>Logger.new_logger Logger.root_logger "HOCLP"\<close>


ML_file\<open>util.ML\<close>

ML_file\<open>container.ML\<close>
ML_file\<open>node.ML\<close>
ML_file\<open>alternating_linked_containers.ML\<close>
ML_file\<open>alternating_linked_containers_zipper.ML\<close>
(* ML_file\<open>state.ML\<close> *)
ML_file\<open>hoclp.ML\<close>

ML\<open>
  structure Util = HOCLP_Util
  @{functor_instance struct_name = HOCLPDT
    and functor_name = HOCLP
    and id = \<open>"dt"\<close>
    and more_args = \<open>structure TI = Discrimination_Tree\<close>}
  open HOCLPDT
\<close>

ML_file\<open>hoclp_tactic.ML\<close>

ML\<open>
  val compose_move = Option.composePartial
  val repeat_move = perhaps_loop
  fun move_to_origin_base move_up1 move_up2 move_left =
    apply2 repeat_move (move_left, compose_move (move_up2, move_up1))
    |> compose_move
  fun move_to_origin_path_tree_zipper path_zipper = move_to_origin_base
    move_up_path_tree_zipper move_up_path_tac_tree_zipper move_left_path_tree_zipper path_zipper
\<close>

ML\<open>
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
- retrival: check for assumptions and goal or only check for goal and solve assumptions
- visiting the same goal twice without an answer -> fail
*)



end
