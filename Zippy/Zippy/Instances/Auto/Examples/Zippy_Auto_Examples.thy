\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Examples and Brief Technical Overview for Zippy Auto\<close>
theory Zippy_Auto_Examples
  imports
    HOL.List
    Zippy_Auto_HOL
begin

paragraph \<open>Summary\<close>
text \<open>The @{method zippy} method (full name: \<^emph>\<open>Zippy Auto\<close>) is a customisable general-purpose
white-box prover based on the Zippy framework. This theory begins with examples demonstrating some
key features and concludes with a brief technical overview for users interested in customising the
method.

On a high-level, @{method zippy} performs a proof tree search with customisable
expansion actions and search strategies. By default, it uses an \<open>A\<^sup>*\<close> search and integrates the
classical reasoner, simplifier, the blast prover, and supports resolution with higher-order and
certifying unification, conditional substitutions, case splitting and induction, among other things.

In most cases, @{method zippy} can be used as a drop-in replacement for Isabelle's classical methods
like @{method auto}, @{method fastforce}, @{method force}, @{method fast}, etc.,
as demonstrated in @{dir Benchmarks}. Note, however, that @{method zippy} can be slower than those
methods due to a more general search procedure.

Like @{method auto}, @{method zippy} supports non-terminal calls and interactive proof exploration.\<close>

subsection \<open>Examples\<close>

text \<open>Note: some examples in this files are adapted from @{theory HOL.List}.\<close>

experiment
begin

text \<open>You can use it like @{method auto}:\<close>

lemma "sorted_wrt (>) l \<longleftrightarrow> sorted (rev l) \<and> distinct l"
  by (induction l) (zippy iff: antisym_conv1 simp: sorted_wrt_append)

text \<open>You can use it for proof exploration (i.e. the method returns incomplete attemps):\<close>

lemma
  assumes [intro]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  apply zippy
  back
  back
  oops

text \<open>Note that the method returned the goal @{prop "B \<Longrightarrow> Q"} but not @{prop "B \<Longrightarrow> P"}.
The reason is that, by default, the method only returns those incomplete attempts that only use
"promising" expansions on its search path, as further elaborated in the technical overview.
The simplifier, for instance, is marked as a "promising" expansion action.
For the classical reasoner, expansions with unsafe (introduction) rules are not marked as promising
while safe rules are.

One can instruct the method to return all attempts by changing its default strategy from
@{ML Zippy.Run.AStar.promising'} to @{ML Zippy.Run.AStar.all'}:\<close>

lemma
  assumes [intro]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  apply (zippy run exec: Zippy.Run.AStar.all')
  oops

text \<open>Alternatively, the introduction rule can be marked as safe:\<close>

lemma
  assumes [intro!]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  apply zippy
  oops

text \<open>Many explorations are possibly infinite or too large for an exhaustive search. In such cases,
one may limit the number of expansion steps. Below, we fuel the method with 20 steps:\<close>

lemma
  assumes [intro]: "P \<and> P \<Longrightarrow> P"
  shows "P"
  apply (zippy 20 run exec: Zippy.Run.AStar.all') \<comment>\<open>Note: loops if no limit is passed\<close>
  oops

text \<open>One can also limit the maximum search depth, e.g. to depth 2:\<close>

lemma
  assumes [intro]: "P \<and> P \<Longrightarrow> P"
  shows "P"
  apply (zippy run exec: "Zippy.Run.AStar.all 2") \<comment>\<open>Note: loops if no depth limit is passed\<close>
  oops

text \<open>You can perform case splits:\<close>

lemma "tl xs \<noteq> [] \<longleftrightarrow> xs \<noteq> [] \<and> \<not>(\<exists>x. xs = [x])"
  by (zippy cases xs)

fun foo :: "nat \<Rightarrow> nat" where
  "foo 0 = 0"
| "foo (Suc _) = 1"

lemma "foo n + foo m < 4"
  by (zippy cases n and m)

text \<open>You may also use patterns of the shape (pattern, anti-patterns):\<close>

lemma "foo n + foo m < 4"
  \<comment> \<open>matches natural numbers, but no applications (e.g. @{term "foo n"})\<close>
  by (zippy cases (pat) ("_ :: nat", "_ _"))

text \<open>You may even use predicates:\<close>

lemma "foo n + foo m < 4"
  by (zippy cases (pred) "member (op =) [@{term n}, @{term m}]")

text \<open>You can use induction:\<close>

lemma "foo n + foo m < 4"
  by (zippy induct rule: foo.induct)

text \<open>Again, you may also use patterns and predicates:\<close>

lemma "foo n + foo m < 4"
  by (zippy induct (pat) ("_ :: nat", "_ _"))

text \<open>Here are some more complex combinations (the original code is marked with ORIG). Note that
configurations for different actions are separated by \<^emph>\<open>where\<close>.\<close>

lemma list_induct2:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (x#xs) (y#ys))
   \<Longrightarrow> P xs ys"
  by (zippy induct xs arbitrary: ys where cases (pat) "_ :: _ list")
(*ORIG*)
(* proof (induct xs arbitrary: ys)
  case (Cons x xs ys) then show ?case by (cases ys) simp_all
qed simp *)

lemma list_induct2':
  "\<lbrakk> P [] [];
  \<And>x xs. P (x#xs) [];
  \<And>y ys. P [] (y#ys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#xs) (y#ys) \<rbrakk>
 \<Longrightarrow> P xs ys"
  by (zippy induct xs arbitrary: ys where cases (pat) ("_ :: _ list", "[]" "_ _"))
  (*ORIG*)
  (* by (induct xs arbitrary: ys) *)
  (* (case_tac x, auto) *)

text \<open>Data passed as method modifiers can also be stored in the context more generally:\<close>

fun gauss :: "nat \<Rightarrow> nat" where
  "gauss 0 = 0"
| "gauss (Suc n) = n + 1 + gauss n"

(*Note: induction rules are always applicable and should hence only be locally registered*)
context notes gauss.induct[zippy_induct (pat) ("_ :: nat", "_ _")]
begin
lemma "gauss n = (n * (n + 1)) div 2" by zippy

lemma "gauss n < gauss (Suc n)" by zippy

lemma "gauss n > 0 \<longleftrightarrow> n > 0" by zippy
end

text \<open>In some cases, it is necessary (or advisable for performance reasons) to change the search
strategy from the default \<open>A\<^sup>*\<close> search to breadth-first, depth-first, or best-first search:\<close>

lemma list_induct3:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P [] [] [] \<Longrightarrow>
   (\<And>x xs y ys z zs. length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (x#xs) (y#ys) (z#zs))
   \<Longrightarrow> P xs ys zs"
  by (induct xs arbitrary: ys zs)
  (zippy cases (pat) ("_ :: _ list", "[]") where run exec: Zippy.Run.Breadth_First.all')
(*ORIG*)
(* proof (induct xs arbitrary: ys zs)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs) then show ?case by (cases ys, simp_all)
    (cases zs, simp_all)
qed *)

text \<open>One can use conditional substitution rules:\<close>

lemma filter_insort:
  "sorted (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort_key f x xs) = insort_key f x (filter P xs)"
  by (induct xs)
  (zippy subst insort_is_Cons where run exec: Zippy.Run.Best_First.all')
  (* (zippy subst insort_is_Cons) *) (*this also works, but it is slower*)
  (*ORIG*)
  (* (auto, subst insort_is_Cons, auto) *)

lemma rev_eq_append_conv: "rev xs = ys @ zs \<longleftrightarrow> xs = rev zs @ rev ys"
  by (zippy subst rev_rev_ident[symmetric])
  (*ORIG*)
  (* by (metis rev_append rev_rev_ident) *)

lemma dropWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
  dropWhile (\<lambda>y. y \<noteq> x) (rev xs) = x # rev (takeWhile (\<lambda>y. y \<noteq> x) xs)"
  by (zippy induct xs where subst dropWhile_append2)
(*ORIG*)
(* proof (induct xs)
  case (Cons a xs)
  then show ?case
    by(auto, subst dropWhile_append2, auto)
qed simp *)

text \<open>One can pass (elim-/dest-/forward-)rules that should be resolved by Isabelle's standard
higher-order unifier, matcher, or a customisable certifying unifier (cf. @{session ML_Unification}).
In contrast to the rules passed to the classical reasoner, each such rule can be annotated with
individual data, e.g. priority, cost, and certifying unifier to be used.

Resolving rules with a certifying unifier is particularly useful in situations where equations do
not hold up to \<open>\<alpha>\<beta>\<eta>\<close>-equality but some stronger, provable equality (see the examples theories in
@{session ML_Unification} for more details). By default, the certifying unifier
@{ML Standard_Mixed_Comb_Unification.first_higherp_comb_unify} is used, which uses the simplifier
and unification hints (cf. @{theory ML_Unification.ML_Unification_Hints}), among other things.\<close>

lemma
  assumes "Q"
  and [simp]: "Q = P"
  shows "P"
  by (zippy urule assms)
  (*below call does not work: P does not unify with Q*)
  (* by (zippy rule assms) *)

text \<open>Passing rules to \<open>urule\<close> is particularly useful when dealing with definitions. In such
cases, theorems for the abbreviated concept can re-used for the new definition (without making the
definition opaque in general, as is the case with @{command abbreviation}):\<close>

definition "my_refl P \<equiv> reflp_on {x. P x}" (*some derived concept*)

(*register a unification hint to the certifying unifier*)
lemma my_refl_uhint [uhint]:
  assumes "{x. P x} \<equiv> S"
  shows "my_refl P \<equiv> reflp_on S"
  using assms unfolding my_refl_def by simp

lemma "my_refl P Q \<Longrightarrow> P x \<Longrightarrow> \<exists>x. Q x x"
  by (zippy urule (d) reflp_onD) (*we can directly use the theorem reflp_onD as a destruction rule*)

text \<open>For very fine-grained control, one can even specify individual functions to initialise the
proof trees linked to the rule's side conditions. By default, each such tree is again solved by all
expansion actions registered to @{method zippy}. Below, we override that behaviour and let the
rule's second premise be solved by reflexivity instead. You may check the technical overview
section for more details about below code.\<close>

lemma
  assumes "P \<Longrightarrow> U = U \<Longrightarrow> Q"
  shows "A \<longrightarrow> Q"
  apply (zippy rule assms updates: [2: \<open>fn i =>
    let open Zippy; open ZLPC Base_Data MU; open SC A
      val id = @{binding "refl"}
      val a_meta = AMeta.metadata (id, Lazy.value "proof by reflexivity")
      fun mk_aa_meta _ _ = AAMeta.metadata {cost = Cost.VERY_LOW, progress = AAMeta.P.Promising}
      fun ztac _ = Ctxt.with_ctxt (fn ctxt => arr (resolve_tac ctxt @{thms refl}
        |> Tac_AAM.lift_tac mk_aa_meta |> Tac_AAM.Tac.zSOME_GOAL_FOCUS))
    in
      Tac.cons_action_cluster Util.exn (ACMeta.no_descr id) [(GFocus.single i, {
        empty_action = Library.K Zippy.PAction.disable_action,
        meta = a_meta,
        result_action = Result_Action.action (Library.K (C.id ()))
          Result_Action.copy_update_data_empty_changed,
        presultsq = Zippy_Auto.PResults.enum_scale_presultsq_default Cost.LOW,
        tac = ztac})]
      >>> (the #> Up3.morph)
    end\<close>])
  back
  oops

text \<open>Zippy uses the @{ML_structure Logger} from @{theory ML_Unification.ML_Logger}. You can use it
to trace its search. Check the logger's examples theory in @{session ML_Unification} for a
demonstration how to filter and modify the logger's output.\<close>

lemma
  assumes [intro]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.DEBUG\<close>]]
  apply zippy
  oops


subsection \<open>Technical Overview\<close>

text \<open>
The method @{method zippy} is based on the Zippy framework. For a preprint about the latter see
\<^cite>\<open>zippy\<close>. On a high-level, the method has three phases:

\<^enum> Initialise the proof tree for a given goal.
\<^enum> Repeatedly expand and modify nodes of the proof tree.
\<^enum> Extract discovered theorems from the proof tree.

The particularities of the expansion (e.g. order of expansion, expansion rules, search bounds)
are largely customisable. Some configuration possibilities are demonstrated above.

During initialisation, the proof tree is (typically) augmented with action clusters. Each action
cluster stores a set of prioritised actions (short: \<^emph>\<open>pactions\<close>; cf. @{ML_functor Zippy_PAction_Mixin_Base}).
A paction consists of a priority and a function modifying the proof tree, called an \<^emph>\<open>action\<close>.
The paction's priority can be used to select action candidates during search.

By default, the tree is initialised with the set of initialisation functions registered in
@{ML_structure Zippy_Auto.Run.Init_Goal_Cluster}. The current registrations can be seen as follows:
\<close>

ML_val\<open>Zippy_Auto.Run.Init_Goal_Cluster.Data.get_table (Context.the_generic_context ())\<close>

text \<open>A registration requires an identifier and an initialisation function modifying the proof
tree in the desired way. Below, we register and delete an initialisation that adds an action cluster
with a single paction, capable of closing goals by reflexivity:\<close>

declare [[zippy_init_gc \<open>
  let open Zippy; open ZLPC MU; open A Mo
    val id = @{binding refl}
    (*action cluster metadata*)
    val ac_meta = Mixin_Base3.Meta.Meta.metadata (id, Lazy.value "reflexivity action cluster")
    (*action metadata*)
    val a_meta = Mixin_Base4.Meta.Meta.metadata (id, Lazy.value "proof by reflexivity")
    (*action application metadata*)
    fun mk_aa_meta _ _ = Base_Data.AAMeta.metadata {cost = Cost.VERY_LOW, (*cost of the action's result*)
      progress = Base_Data.AAMeta.P.Promising} (*is it a promising expansion?*)
    fun ztac _ = Ctxt.with_ctxt (fn ctxt => arr (resolve_tac ctxt @{thms refl}
      |> Tac_AAM.lift_tac mk_aa_meta |> Tac_AAM.Tac.zSOME_GOAL_FOCUS))
    val data = {
      (*disable the action once the tactic returns no results*)
      empty_action = Library.K PAction.disable_action,
      meta = a_meta,
      (*attach a new node from the tactic's result and, for every remaining subgoal, copy the actions
      registered for those subgoals from the node's parent*)
      result_action = Result_Action.action (Library.K (C.id ()))
        Result_Action.copy_update_data_empty_changed,
      (*the sequence of priorities for each pull from the tactic's result sequence*)
      presultsq = Zippy_Auto.PResults.enum_scale_presultsq_default Cost.LOW,
      tac = ztac}
    (*attach the action cluster and step back to the parent node*)
    fun init _ focus z = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.no_descr id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zippy_init_gc del: "@{binding refl}"]] (*delete it*)

text \<open>Since the kind of pactions tried by zippy is extensible, the parser of @{method zippy} is also
extensible. Each parser has to apply its desired changes to the context and return a unit:
\<close>

declare [[zippy_parse add: \<open>(@{binding refl},
  apfst (Config.put_generic Unify.search_bound 5) (*change the search bound*)
  #> tap (fn _ => writeln "I got parsed!") #> Scan.succeed ())\<close>]]

lemma "x = x"
  by (zippy refl) (*put your cursor on the method*)

declare [[zippy_parse del: \<open>@{binding refl}\<close>]] (*delete it again*)

text \<open>The initialised proof tree can then be expanded. By default, an \<open>A\<^sup>*\<close> search is performed,
taking into consideration the pactions' user supplied priorities and the sum of costs of the path
leading to a paction. Other available search strategies are depth-first and breadth-first search
with \<open>A\<^sup>*\<close>-cost tiebreakers, and best-first search on the pactions' priorities. Other search
strategies may at will.

For more details, check the sources of the setup in @{theory Zippy.Zippy_Auto_Pure} and
@{theory Zippy.Zippy_Auto_HOL}.\<close>

end
end
