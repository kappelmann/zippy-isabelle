(*  Title:      Zippy/cases_tactic.ML
    Author:     Kevin Kappelmann
*)
signature CASES_TACTIC =
sig
  include HAS_LOGGER
  val cases_lifted_insts_tac : bool -> thm option -> term option list -> thm list ->
    Proof.context -> int -> tactic
  val cases_pattern_tac : bool -> Unification_Base.matcher -> thm option ->
    (term * term list) option list -> thm list -> Proof.context -> int -> tactic
end

functor Cases_Tactic(
    val get_casesP : Proof.context -> thm list -> thm list
    val get_casesT : Proof.context -> typ list -> term option list -> thm list
    val trivial_tac : Proof.context -> int -> tactic
  ) : CASES_TACTIC =
struct

val logger = Logger.setup_new_logger Logger.root "Cases_Tactic"

structure Show = SpecCheck_Show

fun rev_vars_of tm = Term.fold_aterms (fn t as Var _ => insert (op =) t | _ => I) tm []

val pretty_inst = Show.list o Show.option o Show.term

(*adapted from induct.ML to work on fixed instances possibly containing loose bvars from the subgoal*)
fun cases_lifted_insts_tac simp opt_rule insts facts ctxt =
  let fun tac (binders, prems) i st = Seq.make (fn _ =>
    let
      val nvars_subgoal_prems = Logic.mk_conjunction_list prems |> rev_vars_of |> length
      val nfacts = length facts
      fun inst_rule r =
        let
          val (_, consumes) = Rule_Cases.get r
          val m = Int.min (nfacts, consumes)
          val (thms, facts) = chop m facts
          val st = Method.insert_tac ctxt facts i st |> Seq.hd
          val r_lifted = Drule.incr_indexes st r |> Thm.lift_rule (Thm.cprem_of st i)
          val insts = insts
            |> map (Option.map (curry Logic.rlist_abs binders #> Thm.cterm_of ctxt))
            |> append (replicate nvars_subgoal_prems NONE)
          val r_lifted = Drule.infer_instantiate' ctxt insts r_lifted
          val comp_nprems = let val nprems_diff = Thm.nprems_of r - Thm.nprems_of r_lifted
            in fn r_lifted_resolved => Thm.nprems_of r_lifted_resolved + nprems_diff end
        in
          HEADGOAL (RANGE (map (single #> resolve_tac ctxt) thms)) r_lifted
          |> Seq.map (rpair (comp_nprems, st))
        end
      val rulesq = case opt_rule of
          SOME r => inst_rule r
        | NONE =>
            let
              val rules = get_casesP ctxt facts @ get_casesT ctxt (map snd binders) insts
              val _ = if null rules
                then @{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
                    Pretty.block [Pretty.str "Could not find case rules for instantiations ",
                      pretty_inst ctxt insts],
                    Pretty.block [Pretty.str "and facts ", Show.list (Show.thm ctxt) facts]
                  ] |> Pretty.block0 |> Pretty.string_of)
                else @{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
                    Pretty.str "Found case rules",
                    Show.list (Thm.pretty_thm ctxt) rules,
                    Pretty.str "for instantiations",
                    pretty_inst ctxt insts
                  ] |> Pretty.block |> Pretty.string_of)
            in Seq.of_list rules |> Seq.maps (Seq.try inst_rule) |> Seq.flat end
      fun resolve_tac thm nprems = Tactic_Util.no_lift_resolve_tac thm nprems ctxt
    in
      rulesq
      |> Seq.maps (fn (rule, (comp_nprems, st)) => (resolve_tac rule (comp_nprems rule)
        THEN_ALL_NEW (if simp then TRY o trivial_tac ctxt else K all_tac)) i st)
      |> Seq.pull
    end)
  in Tactic_Util.SUBGOAL_STRIPPED (apsnd fst) tac end

fun pretty_pattern ctxt (p, no_ps) = Pretty.breaks [
    Pretty.block [Pretty.str "Pattern: ", Show.term ctxt p],
    Pretty.block [Pretty.str "No patterns: ", Show.list (Show.term ctxt) no_ps]
  ] |> Pretty.block0

local
  structure ListT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(\<^eval>\<open>sfx_ParaT_nargs "List_Monad_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>)))
in
fun cases_pattern_tac simp match opt_rule patterns facts ctxt =
  let fun tac subgoal i st = Seq.make (fn _ =>
    let
      val params = Logic.strip_params subgoal
      val (paramTs, (binders, binderTs, nbinders)) = fold_map
        (fn p => fn (rev_ps, rev_psT, i) => let val pT = snd p
          in (pT, (p :: rev_ps, pT :: rev_psT, i + 1)) end)
        params ([], [], 0)
      val (binders, ctxt) = Binders.fix_binders binders ctxt
      val prepare_pattern = Logic.incr_indexes (paramTs, Thm.maxidx_of st + 1)
        #> `(Term.maxidx_of_term #> Envir.empty)
      val patterns = patterns
        |> map (Option.map (fn (p, no_ps) => (prepare_pattern p, map prepare_pattern no_ps)))
      val matches = can (fn ((env, p), t) =>
        Unification_Util.unify_types ctxt (apply2 (curry type_of1 binderTs) (p, t)) env
        |> match binders ctxt (p, t) |> Seq.hd)
      fun select (p, no_ps) t = not (loose_bvar (t, nbinders)) andalso matches (p, t)
        andalso forall (fn p => not (matches (p, t))) no_ps
      val selects = map_filter (Option.map select) patterns
      fun merge [] [] = []
        | merge (NONE :: _) [] = []
        | merge (NONE :: ps) ts = NONE :: merge ps ts
        | merge (SOME _ :: ps) (t :: ts) = SOME t :: merge ps ts
        | merge _ _ = error "unreachable code in cases_pattern_tac"
      val insts = find_subterms selects subgoal |> map rev
      val _  = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
          Pretty.block [Pretty.str "Found instances ",
            Show.list (Show.list (Show.term ctxt)) insts],
          Pretty.block [Pretty.str "for patterns ",
            Show.list (pretty_pattern ctxt)
              (map_filter (Option.map (apfst snd #> apsnd (map snd))) patterns)]
        ] |> Pretty.block |> Pretty.string_of)
    in
      ListT.traverse I insts |> Seq.of_list (*compute subterm combinations*)
      |> Seq.map (merge patterns)
      |> Seq.maps (fn insts => cases_lifted_insts_tac simp opt_rule insts facts ctxt i st)
      |> Seq.pull
    end)
  in Tactic_Util.SUBGOAL_DATA I tac end
end

end
