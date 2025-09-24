\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Auto_HOL
  imports
    Zippy_Instance_Auto
    Zippy_Instance_Classical
begin

paragraph \<open>Classical Reasoner\<close>

ML\<open>
local structure Zippy_Classical = Zippy_Instance_Classical(structure Z = Zippy; structure Ctxt = Z.Ctxt)
in structure Zippy = struct open Zippy Zippy_Classical end end
\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy; open ZLP MU; open SC
    val id = @{binding classical_slow_step}
    val prio_sq_co_safe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.VERY_HIGH
    val prio_sq_co_unsafe = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.MEDIUM
    val prio_sq_co_atomize_prems = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.HIGH
    val data = Classical.slow_step_atomize_prems_data Util.exn id prio_sq_co_safe
      prio_sq_co_unsafe prio_sq_co_atomize_prems
    fun init _ focus = Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)]
      >>> Up3.morph
  in (id, init) end\<close>]]

declare [[zippy_parse add: \<open>(@{binding clasimp}, Clasimp.clasimp_modifiers |> Method.sections)\<close>
  and default: \<open>@{binding clasimp}\<close>]]

paragraph \<open>Blast\<close>

ML\<open>
structure Zippy_Auto =
struct open Zippy_Auto
structure Blast =
struct
val depth_limit = Attrib.setup_config_int (Binding.make (FI.prefix_id "blast_depth", @{here})) (K 4)
val parse = Scan.depend (fn context =>
  Parse.int >> `(fn i => Config.put_generic depth_limit i context))
end
end
\<close>

declare [[zippy_init_gcs \<open>
  let
    open Zippy; open ZLP MU; open SC A
    val id = @{binding blast}
    (*TODO time limit?*)
    fun tac ctxt i state = Seq.make (fn _ =>
      let val depth = Config.get ctxt Zippy_Auto.Blast.depth_limit
      in Blast.depth_tac ctxt depth i state |> Seq.pull end)
    fun ztac ctxt = Tac_AAM.lift_tac_progress Base_Data.AAMeta.P.promising (tac ctxt)
      |> Tac_AAM.Tac.zTRY_EVERY_FOCUS1_NONE_ALL_GOALS1 Tac_AAM.madd
    val mk_cud = Result_Action.copy_update_data
    val data = {
      empty_action = Library.K (PResults.empty_action Util.exn),
      meta = Mixin4.Meta.Meta.empty id,
      result_action = Result_Action.action (Library.K (C.id ())) mk_cud,
      prio_sq_co = PResults.enum_halve_prio_halve_prio_depth_sq_co Prio.LOW,
      tac = Ctxt.with_ctxt (ztac #> arr)}
    fun init_ac _ focus =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.empty id) [(focus, data)] >>> Up3.morph
  in (id, init_ac) end\<close>]]

declare [[zippy_parse add: \<open>(@{binding blast}, Zippy_Auto.Blast.parse >> K ())\<close>]]

lemma assumes h: "P"
  shows "P"
  apply (zippy 1 intro!: h where blast 0) (*TODO: better parsing for blast with time limit*)
  done

end
