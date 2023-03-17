\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Higher-Order Constraint Logic Programming\<close>
theory Constraint_Logic_Programming
  imports
    Logging.Logging
    Logging.ML_Attributes
    Term_Indexing.Term_Indexing
    Universal_Data.Universal_Data
    SpecCheck.SpecCheck_Show
    (*Main*)
begin

paragraph \<open>Summary\<close>
text \<open>A higher-order constraint logic programming tactic.\<close>

ML_file\<open>util.ML\<close>
ML_file\<open>clp.ML\<close>

ML\<open>
  structure Util = Constraint_Logic_Programming_Util
  structure CLPDT = Constraint_Logic_Programming(Discrimination_Tree)
\<close>
declare[[ML_dattr "fn _ => Logger.set_log_level CLPDT.logger Logger.ALL"]]
declare[[eta_contract=false]]

theorem test:
  assumes "k \<equiv> k"
  shows "\<lambda>x. f x \<equiv> (\<lambda>y. g ((\<lambda>z. z) y) c) (\<lambda>y. d y)"
  sorry

ML\<open>
  fun update_clp_rule_code op_code clp_tacs =
    let
      val thm_name = Util.internal_code_name "thm"
      val code = flat [
          ML_Lex.read (Util.spaces ["fn", thm_name, "=> ("]),
          op_code,
          ML_Lex.read ") (",
          CLPDT.clp_tactics_code clp_tacs,
          ML_Lex.read (implode [", ", thm_name, ")"])
        ]
    in code end
  fun run_update_clp_rule_code op_code context clp_tacs thm pos =
    let
      val update_code = update_clp_rule_code op_code clp_tacs
      val context' = Util.put_univ_thm thm context
        |> Util.run_get_data_update_context_code Util.get_univ_thm_code update_code pos
    in context' end
  fun add_clp_rule (clp_tacs, pos) thm context =
    let
      val num_clp_tacs = length clp_tacs
      val nprems = Thm.nprems_of thm
    in
      if num_clp_tacs <> nprems
      then error (implode [
          "Number of passed CLP tactics (",
          string_of_int num_clp_tacs,
          ") not equal to number of theorem premises (",
          string_of_int nprems,
          ")"
        ])
      else
        let val add_code = ML_Lex.read "CLPDT.add_clp_rule"
        in run_update_clp_rule_code add_code context clp_tacs thm pos end
    end
  fun delete_clp_rule (clp_tacs, pos) thm context =
    let
      val num_clp_tacs = length clp_tacs
      val nprems = Thm.nprems_of thm
      val _ = if num_clp_tacs <> nprems
        then @{log Logger.WARN Logger.root_logger} (Context.proof_of context) (fn _ => implode [
            "Number of passed CLP tactics (",
            string_of_int num_clp_tacs,
            ") not equal to number of theorem premises (",
            string_of_int nprems,
            ")"
          ])
        else ()
      val delete_code = ML_Lex.read "CLPDT.delete_clp_rule"
      in run_update_clp_rule_code delete_code context clp_tacs thm pos end
  val parse_ml_pos = Scan.repeat Parse.embedded_ml |> Util.parse_position
  fun parse_attr update = parse_ml_pos >> (Thm.declaration_attribute o update)
  val parse = Args.add |-- parse_attr add_clp_rule
    || Args.del |-- parse_attr delete_clp_rule
    || parse_attr add_clp_rule
  val _ = Attrib.setup @{binding clp} (Scan.lift parse) "CLP rule" |> Theory.setup
\<close>

ML\<open>
  val clptac = CLPDT.print_clp_tactic
\<close>

lemma abc [clp add]:
  shows "F \<equiv> L N"
  sorry

declare abc[clp del]

lemma ab [clp add clptac clptac] :
  assumes "A \<equiv> B"
  and "C \<equiv> D E"
  shows "F \<equiv> L N"
  and "Z \<equiv> Y"
  sorry

declare ab[clp clptac clptac]

ML\<open>
  (* val context = CLPDT.add_print_clp_rule @{thm abc(1)} (Context.Proof @{context}) *)
  (* val context = CLPDT.add_print_clp_rule @{thm abc(1)} (Context.Proof @{context}) *)
  (* val context = CLPDT.remove_print_clp_rule @{thm abc(2)} (Context.Proof @{context}) *)
  (* val context = CLPDT.add_print_clp_rule @{thm abc(1)} context *)
  val context = (Context.Proof @{context})
  val {rules = a} = CLPDT.CLP_Rules_Data.get context
    |> CLPDT.dest_clp_rules
  val b = Discrimination_Tree.content a |> map @{print}
\<close>

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
