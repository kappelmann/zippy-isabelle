\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Constraing Logic Programming\<close>
theory Constraint_Logic_Programming
  imports
    Logging.Logging
    Term_Indexing.Term_Indexing
begin

paragraph \<open>Summary\<close>
text \<open>A constraint logic programming tactic.\<close>

ML_file\<open>clp.ML\<close>

ML\<open>
  structure CLPDT = Constraint_Logic_Programming(Discrimination_Tree)
\<close>
(* config[CLPDT.Logger.log_level=Root_Logger.ALL] *)
config[eta_contract=false]

theorem test: "\<lambda>x. f x \<equiv> (\<lambda>y. g ((\<lambda>z. z) y) c) (\<lambda>y. y d)"
  sorry

ML\<open>
  val a = CLPDT.CLP_Rules_Data.get (Context.the_generic_context ())
\<close>

(* setup\<open>CLPDT.add_clp_rule @{thm test} |> Context.theory_map\<close> *)
ML\<open>
  val mythm = @{thm test}
  val myintattr = Attrib.setup_config_int @{binding "myint"} (K 0)
\<close>

ML\<open>
  structure Tint = Theory_Data (
    type T = int
    val empty = 0
    fun merge (i1, i2) = Integer.max i1 i2
  )
\<close>

(* ML\<open>
  val _ = Theory.setup (Tint.put 1)
\<close>

ML\<open>
  val i = Tint.get @{theory}
\<close> *)

ML\<open>
  val a = CLPDT.CLP_Rules_Data.get (Context.Proof @{context})
  (* fun goal_of ctxt = *)
    (* Proof.goal (Toplevel.proof_of (Toplevel.presentation_state ctxt)) |> #goal *)
  fun pretty_thm context thm = Thm.pretty_thm (Context.proof_of context) thm |> Pretty.writeln
  fun printmyint context = @{print} ("myint", Config.get (Context.proof_of context) myintattr)
  fun printtint context = @{print} ("tint", Tint.get (Context.theory_of context))
  fun puttint i context = Tint.put i (Context.theory_of context)
    |> Context.Theory
    |> tap printtint
\<close>

ML\<open>
  fun attr (context, thm) = (@{print} "asm"; pretty_thm context thm;
    printmyint context;
    printtint context;
    Thm.tag ("asm", "added") (puttint 1 context, thm))
  fun s (context, ts) =
    (attr, (context, [List.last ts]))
    (* (@{print} (map Token.print ts); (attr, (context, [List.last ts]))) *)
  val m = Attrib.setup @{binding clp_asm} s "CLP asm"
  val _ = Theory.setup m
\<close>

ML\<open>
  fun attr (context, thm) = (@{print} "concl"; pretty_thm context thm; printmyint context;
    printtint context;
    Thm.tag ("concl", "added") (context, thm))
  fun s (context, ts) =
    (attr, (context, [List.last ts]))
    (* (@{print} (map Token.print ts); (attr, (context, [List.last ts]))) *)
  val m = Attrib.setup @{binding clp_concl} s "CLP concl"
  val _ = Theory.setup m
\<close>

ML\<open>
  fun fattr source thm context =
    let
      val _ = @{print} "toplevel lemma"
      val _ = pretty_thm context thm
      val _ = printmyint context
      val _ = printtint context;
      val rs = ML_Lex.read "("
        @ (ML_Lex.read_source source)
        @ ML_Lex.read ") (Context.the_generic_context ()) |> (Context.put_generic_context o SOME)"
      val context' = ML_Context.expression (Input.pos_of source) rs context
    in context' end
  fun attr ((_, x) :: xs) = Thm.declaration_attribute (fattr x)
  val p = Args.name --| Args.$$$ "=" -- Parse.embedded_input
    |> Parse.and_list
  val s = Scan.lift p
    >> attr
    (* >> (fn args => (@{print} args; attr args)) *)
  val m = Attrib.setup @{binding clp} s "CLP rule"
  val _ = Theory.setup m
\<close>

config[Thm.show_tags=true]
declare[[show_hyps=true]]

lemma abc [tagged "toplevel" "?", clp a="CLPDT.add_clp_rule mythm"]:
  assumes [tagged "asm" "1", clp_asm 1]: "A \<equiv> B"
  and [tagged "asm" "2", clp_asm 2]: "C \<equiv> D E"
  shows [tagged "concl" "1", clp_concl 3]: "F \<equiv> L O"
  and [tagged "concl" "2", clp_concl 4]: "H \<equiv> J I \<Longrightarrow> Z \<equiv> Y"
  sorry

print_theorems
ML\<open>
  (* val a = CLPDT.CLP_Rules_Data.get (Context.Proof @{context}) *)
  val b = Config.get @{context} myintattr
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
