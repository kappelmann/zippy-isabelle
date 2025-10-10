(*  Title:      Zippy/induction_tactic.ML
    Author:     Kevin Kappelmann
*)
signature INDUCTION_TACTIC =
sig
  include HAS_LOGGER
  val induct_tac : bool -> thm list option -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list -> Proof.context -> int -> tactic
  val induct_find_tac : bool -> thm option -> (term -> bool) option list -> (term -> bool) ->
    term option list -> thm list -> Proof.context -> int -> tactic
  val induct_pattern_tac : bool -> Unification_Base.matcher -> thm option ->
    (term * term list) option list -> term list * term list -> term option list ->
    thm list -> Proof.context -> int -> tactic
end

functor Induction_Tactic(Induct : INDUCT) : INDUCTION_TACTIC =
struct

val logger = Logger.setup_new_logger Logger.root "Induction_Tactic"

structure Show = SpecCheck_Show
structure ZTac_Util = Zippy_ML_Tactic_Util

fun pretty_insts ctxt = Show.list (Show.list (Show.option (snd #> fst #> Show.term ctxt)))

(*adapted from induct.ML*)
local open Induct
fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (take n xs ~~ ys) end
fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (drop (m - n) xs ~~ ys) end
fun prep_inst ctxt align tune (tm, ts) =
  let
    fun prep_var (Var (x, xT), SOME t) =
          let
            val ct = Thm.cterm_of ctxt (tune t)
            val tT = Thm.typ_of_cterm ct
          in
            if Type.could_unify (tT, xT) then SOME (x, ct)
            else error (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Syntax.pretty_term ctxt (Thm.term_of ct), Pretty.str " ::", Pretty.brk 1,
              Syntax.pretty_typ ctxt tT]))
          end
      | prep_var (_, NONE) = NONE
    val xs = vars_of tm
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end
fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = Name.clean (Variable.revert_fixed ctxt z)
        fun index _ [] = []
          | index i (y :: ys) =
              if x = y then x ^ string_of_int i :: index (i + 1) ys
              else y :: index i ys
        fun rename_params [] = []
          | rename_params ((y, Type (U, _)) :: ys) =
              (if U = T then x else y) :: rename_params ys
          | rename_params ((y, _) :: ys) = y :: rename_params ys
        fun rename_asm A =
          let
            val xs = rename_params (Logic.strip_params A)
            val xs' =
              (case filter (fn x' => x' = x) xs of
                [] => xs
              | [_] => xs
              | _ => index 1 xs)
          in Logic.list_rename_params xs' A end
        fun rename_prop prop =
          let val (As, C) = Logic.strip_horn prop
          in Logic.list_implies (map rename_asm As, C) end
        val thm' = Thm.renamed_prop (rename_prop (Thm.prop_of thm)) thm
      in [Rule_Cases.save thm thm'] end
  | special_rename_params _ _ ths = ths
fun get_inductP ctxt (fact :: _) = map single (find_inductP ctxt (Thm.concl_of fact))
  | get_inductP _ _ = []
fun rule_instance ctxt inst rule =
  infer_instantiate ctxt (prep_inst ctxt align_left I (Thm.prop_of rule, inst)) rule
in
fun induct_tac simp opt_rules def_insts arbitrary taking facts ctxt i st =
  Seq.make (fn _ =>
  let
    val _  = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
        Pretty.block [Pretty.str "Running induction tactic for rules ",
          Show.option (Show.list (Show.thm ctxt)) opt_rules],
        Pretty.block [Pretty.str "instances: ", pretty_insts ctxt def_insts],
        Pretty.block [Pretty.str "arbitraries: ",
          Show.list (Show.list (Show.zip Pretty.str (Show.typ ctxt))) arbitrary],
        Pretty.block [Pretty.str "takings: ", Show.list (Show.option (Show.term ctxt)) taking],
        Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
      ] |> Pretty.block0 |> Pretty.string_of)
    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list
    val atomized_defs = map (map (Conv.fconv_rule (atomize_cterm defs_ctxt))) defs

    fun inst_rule (concls, r) =
      (if null insts then `Rule_Cases.get r
        else (align_left "Rule has fewer conclusions than arguments given"
          (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
        |> maps (prep_inst ctxt align_right (atomize_term ctxt))
        |> infer_instantiate ctxt) r |> pair (Rule_Cases.get r))
      |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th))

    val ruleq = case opt_rules of
        SOME rs => Seq.single (inst_rule (Rule_Cases.strict_mutual_rule ctxt rs))
      | NONE =>
          let
            val rules = get_inductP ctxt facts @
              map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts)
            val _ = if null rules
              then @{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
                  Pretty.block [Pretty.str "Could not find induction rules for instantiations: ",
                    pretty_insts ctxt def_insts],
                  Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
                ] |> Pretty.block0 |> Pretty.string_of)
              else @{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
                  Pretty.block [Pretty.str "Found induction rules ",
                    Show.list (Show.list (Thm.pretty_thm ctxt)) rules],
                  Pretty.block [Pretty.str "for instantiations: ", pretty_insts ctxt def_insts],
                  Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
                ] |> Pretty.block0 |> Pretty.string_of)
          in
            Seq.of_list rules |> Seq.map_filter (Rule_Cases.mutual_rule ctxt)
            |> Seq.maps (Seq.try inst_rule)
          end

    fun main_tac i st =
      ruleq
      |> Seq.maps (Rule_Cases.consume defs_ctxt (flat defs) facts)
      |> Seq.maps (fn (((_, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            let
              val adefs = nth_list atomized_defs (j - 1)
              val frees = fold (Term.add_frees o Thm.prop_of) adefs []
              val xs = nth_list arbitrary (j - 1)
              val k = nth concls (j - 1) + more_consumes
            in
              Method.insert_tac defs_ctxt (more_facts @ adefs)
              THEN' (if simp
                then rotate_tac k (length adefs)
                  THEN' arbitrary_tac defs_ctxt k (List.partition (member op = frees) xs |> (op @))
                else arbitrary_tac defs_ctxt k xs)
            end)
          THEN' inner_atomize_tac defs_ctxt) j))
        THEN' atomize_tac defs_ctxt) i st
        |> Seq.maps (fn st' => guess_instance ctxt (internalize ctxt more_consumes rule) i st'
          |> Seq.map (rule_instance ctxt taking)
          |> Seq.maps (fn rule' => (resolve_tac ctxt [rule'] i
            THEN PRIMITIVE (singleton (Proof_Context.export defs_ctxt ctxt))) st')))
  in
    (main_tac
    THEN_ALL_NEW ((if simp then simplify_tac ctxt THEN' (TRY o trivial_tac ctxt) else K all_tac)
    THEN_ALL_NEW rulify_tac ctxt)) i st
    |> Seq.pull
  end)
end

fun induct_find_tac simp opt_rule inst_ps arbitrary_p taking facts ctxt =
  let fun tac subgoal i st = Seq.make (fn _ =>
    let
      fun merge [] [] = []
        | merge (NONE :: _) [] = []
        | merge (NONE :: ps) ts = NONE :: merge ps ts
        | merge (SOME _ :: ps) (t :: ts) = SOME (NONE, (t, false)) :: merge ps ts
        | merge _ _ = error "unreachable code in induct_find_insts_tac"
      val insts = ZTac_Util.find_subterms_comb (map_filter I inst_ps) subgoal
      val arbitrary = singleton (fn ps => ZTac_Util.find_subterms ps subgoal) arbitrary_p
        |> map dest_Free
        handle exn as TERM _ =>
          (@{log Logger.ERR} ctxt (fn _ => "Can only set free variables as arbitrary");
          Exn.reraise exn)
    in
      Seq.of_list insts
      |> Seq.map (merge inst_ps)
      |> Seq.maps (fn insts => induct_tac simp (Option.map single opt_rule) [insts] [arbitrary]
        taking facts ctxt i st)
      |> Seq.pull
    end)
  in Tactic_Util.SUBGOAL_DATA I tac end

fun induct_pattern_tac simp match opt_rule inst_patterns arbitrary_pattern taking facts ctxt =
  let fun tac subgoal i st =
    let
      val params = Logic.strip_params subgoal
      val (paramTs, (binders, binderTs)) = fold_map
        (fn p => fn (rev_ps, rev_psT) => let val pT = snd p
          in (pT, (p :: rev_ps, pT :: rev_psT)) end)
        params ([], [])
      val (binders, ctxt) = Binders.fix_binders binders ctxt
      val prepare_pattern = Logic.incr_indexes (paramTs, Thm.maxidx_of st + 1)
        #> `(Term.maxidx_of_term #> Envir.empty)
      fun prepare_entry (ps, no_ps) = (map prepare_pattern ps, map prepare_pattern no_ps)
      val matches = can (fn ((env, p), t) =>
        Unification_Util.unify_types ctxt (apply2 (curry type_of1 binderTs) (p, t)) env
        |> match binders ctxt (p, t) |> Seq.hd)
      fun matches_pattern (ps, no_ps) t = exists (fn p => (matches (p, t))) ps
        andalso forall (fn p => not (matches (p, t))) no_ps
      fun inst_select p t = not (loose_bvar (t, 0)) andalso matches_pattern p t
      val inst_ps = map (Option.map (apfst single #> prepare_entry #> inst_select)) inst_patterns
      fun arbitrary_select p t = can dest_Free t andalso matches_pattern p t
      val arbitrary_p = prepare_entry arbitrary_pattern |> arbitrary_select
    in induct_find_tac simp opt_rule inst_ps arbitrary_p taking facts ctxt i st end
  in Tactic_Util.SUBGOAL_DATA I tac end

end
