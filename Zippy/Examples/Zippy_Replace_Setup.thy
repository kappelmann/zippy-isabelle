\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Replace_Setup
  imports
    Zippy.Zippy_Instance_Auto_HOL
begin

paragraph \<open>Summary\<close>
text \<open>Setup for Zippy benchmarks.\<close>

ML\<open>
structure Zippy_Auto_Benchmark =
struct
val logger = Logger.setup_new_logger zippy_base_logger "Zippy_Auto_Benchmark"
val time = Time.now ()
val out_path = Path.basic ("benchmark_" ^ Time.toString time)
val _ = Theory.setup (Context.theory_map
  (Logger.set_output logger (fn _ => fn msg => File.append out_path (msg ^ "\n"))
  #> Logger.set_show_logger logger false))

fun wrap_tac binding tac pos ctxt state =
  if Term_Util.has_dummy_pattern (Thm.concl_of state)
  then no_tac state
  else
    let
      val timeout = seconds 40.0
      fun pretty_pos _ = Pretty.str (Position.properties_of pos |> map Properties.print_eq |> commas)
      val log_ctxt = Config.put Logging_Antiquotation.show_log_pos false ctxt
      val _ = @{log Logger.INFO} log_ctxt (fn _ => Pretty.fbreaks [
          pretty_pos (),
          Pretty.block [Pretty.str "Running: ", Binding.pretty binding]
        ] |> Pretty.block0 |> Pretty.pure_string_of)
      fun run _ = Timeout.apply timeout (tac ctxt) state |> Seq.pull |> Either.Right
        handle Timeout.TIMEOUT time => Either.Left time
      val (timing, res) = Timing.timing run ()
      val _ = @{log Logger.INFO} log_ctxt (fn _ => Pretty.fbreaks (
          pretty_pos () :: (case res of
            Either.Left time => [Pretty.str ("Timeout: " ^ Time.print time)]
          | Either.Right res => [
              Pretty.block [Pretty.str (if is_none res then "Failed: " else "Finished: "), Binding.pretty binding],
              Pretty.str ("Timing: " ^ Timing.message timing)
            ])
        ) |> Pretty.block0 |> Pretty.pure_string_of)
    in case res of
      Either.Left _ => Seq.empty
    | Either.Right res => Seq.make (K res)
    end

fun parse method =
  let val parse_fuel = Parse_Util.option Parse.nat
  in
    Parse_Util.position' (Scan.lift (Scan.option (Parse.nat -- Parse.nat))
    -- Scan.lift parse_fuel
    --| Zippy_Auto.Context_Parsers.parse)
    >> (fn (args, pos) => method args pos)
  end
fun setup method descr binding = Method.local_setup binding (parse method) descr

fun all_existing_tac (_, opt_fuel) ctxt =
  let val HEADGOAL_SOLVED = HEADGOAL o SOLVED'
  in
    if is_none opt_fuel
    then PARALLEL_GOALS (DEPTH_FIRST Thm.no_prems (PARALLEL_CHOICE [
      SOLVE (auto_tac ctxt),
      HEADGOAL_SOLVED (SELECT_GOAL (auto_tac ctxt)),
      HEADGOAL_SOLVED (force_tac ctxt),
      HEADGOAL_SOLVED (fast_force_tac ctxt),
      HEADGOAL_SOLVED (slow_simp_tac ctxt),
      HEADGOAL_SOLVED (best_simp_tac ctxt),
      HEADGOAL_SOLVED (fast_tac ctxt),
      HEADGOAL_SOLVED (slow_tac ctxt),
      HEADGOAL_SOLVED (best_tac ctxt),
      HEADGOAL_SOLVED (asm_full_simp_tac ctxt)]))
    (*keep non-terminal calls as they are since they cannot be solved directly*)
    else Zippy_Auto.Run.tac opt_fuel ctxt
  end

val setups as [setup_zippy, setup_auto, setup_force,
  setup_fastforce, setup_slowsimp, setup_bestsimp,
  setup_fast, setup_slow, setup_best,
  setup_all_existing] =
  let fun mk_entry (binding, mk_tac) = (binding, mk_tac binding)
  in [
    mk_entry (@{binding zippy}, fn b => setup (SIMPLE_METHOD ooo wrap_tac b o Zippy_Auto.Run.tac o snd)
      "Extensible white-box prover based on Zippy"),
    (@{binding auto}, setup (SIMPLE_METHOD ooo K o
      (fn (NONE, _) => CHANGED_PROP o auto_tac
        | (SOME (m, n), _) => (fn ctxt => CHANGED_PROP (mk_auto_tac ctxt m n))))
      "auto"),
    mk_entry (@{binding force}, fn b => setup (SIMPLE_METHOD ooo wrap_tac b o K (REPEAT_FIRST o force_tac))
      "force"),
    (@{binding fastforce}, setup (SIMPLE_METHOD o REPEAT_FIRST ooo K o K fast_force_tac)
      "combined fast and simp"),
    (@{binding slowsimp}, setup (SIMPLE_METHOD o REPEAT_FIRST ooo K o K slow_simp_tac)
      "combined slow and simp"),
    (@{binding bestsimp}, setup (SIMPLE_METHOD o REPEAT_FIRST ooo K o K best_simp_tac)
      "combined best and simp"),
    (@{binding fast}, setup (SIMPLE_METHOD o REPEAT_FIRST ooo K o K fast_tac) "fast"),
    (@{binding slow}, setup (SIMPLE_METHOD o REPEAT_FIRST ooo K o K slow_tac) "slow"),
    (@{binding best}, setup (SIMPLE_METHOD o REPEAT_FIRST ooo K o K best_tac) "best"),
    (@{binding all_existing}, setup (SIMPLE_METHOD ooo K o all_existing_tac)
      "try all existing tactics in parallel")
  ]
  end

val bindings as (binding_adapted :: _) = @{binding adapted} :: map fst setups
fun setup_override f = fold f bindings
val orig_suffix = "_orig"
val setup_origs = fold (fn (b, f) => f (Binding.suffix_name orig_suffix b)) setups
end
\<close>

text \<open>Setup alternative names for original methods.\<close>

local_setup \<open>Zippy_Auto_Benchmark.setup_origs\<close>

text \<open>Override original methods.\<close>

             (*Select the method to use as an override here*)
local_setup \<open>let val method = snd Zippy_Auto_Benchmark.setup_zippy
  in Zippy_Auto_Benchmark.setup_override method end\<close>

end