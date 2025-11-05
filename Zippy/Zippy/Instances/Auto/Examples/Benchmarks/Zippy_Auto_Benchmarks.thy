\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Auto_Benchmarks
  imports
    Zippy.Zippy_Instance_Auto_HOL
begin

paragraph \<open>Summary\<close>
text \<open>Setup for Zippy benchmarks.\<close>

ML\<open>
structure Zippy_Auto_Benchmark =
struct
fun parse method = let val parse_fuel = Parse_Util.option Parse.nat
  in
    Parse_Util.position' (Scan.lift (Scan.option (Parse.nat -- Parse.nat)) (*for auto*)
    -- Scan.lift parse_fuel (*for zippy*)
    --| Zippy_Auto.Context_Parsers.parse) (*for all*)
    >> (fn (args, pos) => method args pos)
  end
fun setup_method method descr binding = Method.local_setup binding (parse method) descr

fun all_existing_tac opt_fuel ctxt = let val HEADGOAL_SOLVED = HEADGOAL o SOLVED'
  in if is_none opt_fuel
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
    (*keep non-terminal calls are since they cannot be solved directly*)
    else Zippy_Auto.Run.tac opt_fuel ctxt
  end

val setups as [setup_zippy, setup_auto, setup_force,
  setup_fastforce, setup_slowsimp, setup_bestsimp,
  setup_fast, setup_slow, setup_best,
  setup_all_existing] = [
    (@{binding zippy}, (Zippy_Auto.Run.tac o snd, "White-box prover based on Zippy")),
    (@{binding auto}, (
      fn (NONE, _) => CHANGED_PROP o auto_tac
        | (SOME (m, n), _) => fn ctxt => CHANGED_PROP (mk_auto_tac ctxt m n),
      "auto")),
    (@{binding force}, (K (REPEAT_FIRST o force_tac), "force")),
    (@{binding fastforce}, (K (REPEAT_FIRST o fast_force_tac), "combined fast and simp")),
    (@{binding slowsimp}, (K (REPEAT_FIRST o slow_simp_tac), "combined slow and simp")),
    (@{binding bestsimp}, (K (REPEAT_FIRST o best_simp_tac), "combined best and simp")),
    (@{binding fast}, (K (REPEAT_FIRST o fast_tac), "fast")),
    (@{binding slow}, (K (REPEAT_FIRST o slow_tac), "slow")),
    (@{binding best}, (K (REPEAT_FIRST o best_tac), "best")),
    (@{binding all_existing}, (all_existing_tac o snd, "try all existing tactics in parallel"))
  ]

fun benchmark_entry binding pos (timing, res) =
  let
    fun elem name children = XML.Elem ((name, []), children)
    val text = XML.Text
    val position = elem "position" (map (fn (k, v) => elem k [text v]) (Position.properties_of pos))
    val binding = elem "binding" [text (Binding.name_of binding)]
    fun mk_timing {elapsed, cpu, gc} = elem "timing" [
      elem "elapsed" [text (Time.print elapsed)],
      elem "cpu" [text (Time.print cpu)],
      elem "gc" [text (Time.print gc)]]
    val result = elem "result" (case res of
        Either.Left time => [elem "timeout" [text (Time.print time)]]
      | Either.Right opt_res => [elem "success" [(text (Value.print_bool (is_some opt_res)))],
          mk_timing timing])
  in elem "entry" [position, binding, result] end

fun wrap_tac binding tac pos ctxt state =
  if Term_Util.has_dummy_pattern (Thm.concl_of state) then no_tac state
  else
    let
      val timeout = seconds 40.0
      fun run _ = Timeout.apply timeout (tac ctxt) state |> Seq.pull |> Either.Right
        handle Timeout.TIMEOUT time => Either.Left time
      val (timing, res) = Timing.timing run ()
      val path = Position.offset_of pos |> the |> string_of_int |> Path.basic
        |> Path.append (Path.basic "zippy_auto_benchmark") |> Path.binding0
      val params = {theory_name = Context.theory_long_name (Proof_Context.theory_of ctxt),
        binding = path, executable = false, compress = false, strict = true}
      val _ = benchmark_entry binding pos (timing, res)
        |> XML.string_of |> XML.Text |> single
        |> Export.export_params (Context.Proof ctxt) params
    in Either.cases (K Seq.empty) (K #> Seq.make) res end

val orig_suffix = "_orig"
val setup_origs = fold (fn (binding, (tac, descr)) => setup_method (SIMPLE_METHOD ooo K o tac) descr
  (Binding.suffix_name orig_suffix binding)) setups

fun setup_wrapped (binding, (tac, descr)) = setup_method
  (SIMPLE_METHOD ooo wrap_tac binding o tac) descr
val setup_override = setup_wrapped #> (fn f => fold f (map fst setups))
end
\<close>

text \<open>Setup alternative names for original methods and override.\<close>

local_setup \<open>Zippy_Auto_Benchmark.setup_origs\<close>
            (*Select the method to use as an override here*)
local_setup \<open>Zippy_Auto_Benchmark.setup_zippy |> Zippy_Auto_Benchmark.setup_override\<close>

end