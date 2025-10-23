\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Replace_Setup
  imports
    Zippy.Zippy_Instance_Auto_HOL
begin

ML\<open>
fun setup_zippy method_binding =
  let open Zippy Zippy_Auto.Run
    val parse_fuel = Parse_Util.option Parse.nat
    val parse = Scan.lift parse_fuel --| Zippy_Auto.Context_Parsers.parse
      >> (Method.SIMPLE_METHOD oo zippy_tac)
  in Method.local_setup method_binding parse "Extensible white-box prover based on Zippy" end

fun setup_auto method_binding =
  let val auto_method =
    Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
      Method.sections clasimp_modifiers >>
    (fn NONE => SIMPLE_METHOD o CHANGED_PROP o auto_tac
      | SOME (m, n) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mk_auto_tac ctxt m n))));
  in Method.local_setup method_binding auto_method "auto" end

local
  fun clasimp_method' tac =
    Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o tac);
in
  fun setup_fastforce binding =
    Method.local_setup binding (clasimp_method' fast_force_tac) "combined fast and simp"
  fun setup_force binding =
    Method.local_setup binding (clasimp_method' force_tac) "force"
  fun setup_fast binding =
    Method.local_setup binding (clasimp_method' fast_tac) "fast"
end
\<close>

local_setup \<open>setup_zippy @{binding auto}\<close>
local_setup \<open>setup_auto @{binding auto_orig}\<close>
local_setup \<open>setup_zippy @{binding fastforce}\<close>
local_setup \<open>setup_fastforce @{binding fastforce_orig}\<close>
local_setup \<open>setup_zippy @{binding force}\<close>
local_setup \<open>setup_force @{binding force_orig}\<close>
local_setup \<open>setup_zippy @{binding fast}\<close>
local_setup \<open>setup_fast @{binding fast_orig}\<close>

end