\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Auto
  imports
    Generic_Table_Data
    Zippy_Instance
    Zippy_Thm_Data
    Main
begin

(*ground polymorphic types since only ground types can be stored in the generic context.*)
setup\<open>let val mk_groundT = K "unit"
in Context.theory_map (ML_Gen.setup_zipper_args' (NONE, SOME mk_groundT) (NONE, SOME mk_groundT)) end\<close>

ML\<open>
signature ZIPPY_RESOLVE_ACTION_DATA_MIXIN_BASE =
  ZIPPY_THM_DATA_MIXIN_BASE
  where type data = @{AllT_args} Zippy.Tac_Util.resolve_action_data

functor Zippy_Resolve_Action_Data_Mixin_Base(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure TI : TERM_INDEX
  ) : ZIPPY_RESOLVE_ACTION_DATA_MIXIN_BASE =
struct
structure FI = Functor_Instance(FI)
structure Data = \<^functor_instance>\<open>functor_name = Zippy_Thm_Data_Mixin_Base
  and id = \<open>FI.id\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    structure Log = Log
    structure TI = TI
    type data = @{AllT_args} Zippy.Tac_Util.resolve_action_data
    val eq_data = K true
    val pretty_data = Zippy.Tac_Util.pretty_resolve_action_data\<close>\<close>
open Data
end

signature ZIPPY_RESOLVE_ACTION_DATA_MIXIN =
sig
  include ZIPPY_RESOLVE_ACTION_DATA_MIXIN_BASE
  structure Thm_Data : ZIPPY_THM_DATA_MIXIN
  where type data = data

  val init_focused_goals_none_all_data : ('a -> Data.term_value list) -> 'a list ->
    Zippy.Tac.GPU.F.focus -> (Zippy.Tac.GPU.F.focus * data) list
  val init_focused_goals_none_no_data : ('a -> Data.term_value list) -> 'a list ->
    Zippy.Tac.GPU.F.focus -> (Zippy.Tac.GPU.F.focus * data) list
end

functor Zippy_Resolve_Action_Data_Mixin(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Res_AC_Data : ZIPPY_RESOLVE_ACTION_DATA_MIXIN_BASE
    val key_of_thm : thm -> term
  ) : ZIPPY_RESOLVE_ACTION_DATA_MIXIN =
struct
open Res_AC_Data
structure FI = Functor_Instance(FI)

\<^functor_instance>\<open>struct_name = Thm_Data
  and functor_name = Zippy_Thm_Data_Mixin
  and id = \<open>FI.prefix_id "thm_data"\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    structure Thm_Data = Res_AC_Data
    val key_of_thm = key_of_thm\<close>\<close>

local open Zippy
in
fun gen_init_focused_goals_data focused_goals lookup x focus = focused_goals focus x
  |> maps (apsnd lookup #>
    (fn (i, datas) => List.map (Thm_Data.term_value_data #> pair (Tac.GPU.F.single i)) datas))
fun init_focused_goals_none_all_data x = gen_init_focused_goals_data
  Tac.GPU.F.focused_goals_none_all x
fun init_focused_goals_none_no_data x = gen_init_focused_goals_data
  Tac.GPU.F.focused_goals_none_no x
end
end
\<close>

ML\<open>
functor Zippy_Auto(structure FI : FUNCTOR_INSTANCE_BASE) =
struct
structure FI = Functor_Instance(FI)
structure Logging =
struct
  val logger = Logger.setup_new_logger zippy_logger FI.name
  local structure Base = struct val parent_logger = logger end
  in
  structure Resolve_Unif_Action_Data = Zippy_Logger_Mixin_Base(open Base
    val name = "Resolve_Unif_Action_Data")
  structure Resolve_Match_Action_Data = Zippy_Logger_Mixin_Base(open Base
    val name = "Resolve_Match_Action_Data")
  structure DResolve_Action_Data = Zippy_Logger_Mixin_Base(open Base
    val name = "DResolve_Action_Data")
  structure EResolve_Action_Data = Zippy_Logger_Mixin_Base(open Base
    val name = "EResolve_Action_Data")
  end
end

type init_action_cluster =
  Zippy.Tac.GPU.F.focus -> (@{ParaT_args} @{AllT_args} Zippy.Z2.zipper) Zippy.emorph

\<^functor_instance>\<open>struct_name = Init_AC_Data
  and functor_name = Generic_Table_Data
  and id = \<open>FI.prefix_id "zauto_init_ac"\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    val parent_logger = Logging.logger
    type key = Zippy_Identifier.id
    val pretty_key = Zippy_Identifier.pretty
    val ord_key = Zippy_Identifier.ord
    type value = Zippy_Thm_State.state * (term list * term) list -> init_action_cluster
    val pretty_value = K (K (Pretty.str "<init action cluster morphism>"))\<close>\<close>
structure Logging =
struct open Logging
  structure Init_AC_Data : ZIPPY_LOGGER_MIXIN_BASE = Init_AC_Data
end

\<^functor_instance>\<open>struct_name = Resolve_Unif
  and functor_name = Zippy_Resolve_Action_Data_Mixin
  and id = \<open>FI.prefix_id "zauto_resolve_unif_action_data"\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    structure Res_AC_Data = \<^functor_instance>\<open>functor_name = Zippy_Resolve_Action_Data_Mixin_Base
      and id = \<open>FI.prefix_id "zauto_resolve_unif_action_data_base"\<close>
      and path = \<open>FI.long_name\<close>
      and more_args = \<open>
        structure Log = Logging.Resolve_Unif_Action_Data
        structure TI = Discrimination_Tree\<close>\<close>
    val key_of_thm = Thm.concl_of\<close>\<close>
\<^functor_instance>\<open>struct_name = Resolve_Match
  and functor_name = Zippy_Resolve_Action_Data_Mixin
  and id = \<open>FI.prefix_id "zauto_resolve_match_action_data"\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    structure Res_AC_Data = \<^functor_instance>\<open>functor_name = Zippy_Resolve_Action_Data_Mixin_Base
      and id = \<open>FI.prefix_id "zauto_resolve_match_action_data_base"\<close>
      and path = \<open>FI.long_name\<close>
      and more_args = \<open>
        structure Log = Logging.Resolve_Match_Action_Data
        structure TI = Discrimination_Tree\<close>\<close>
    val key_of_thm = Thm.concl_of\<close>\<close>

\<^functor_instance>\<open>struct_name = EResolve
  and functor_name = Zippy_Resolve_Action_Data_Mixin
  and id = \<open>FI.prefix_id "zauto_eresolve_action_data"\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    structure Res_AC_Data = \<^functor_instance>\<open>functor_name = Zippy_Resolve_Action_Data_Mixin_Base
      and id = \<open>FI.prefix_id "zauto_eresolve_action_data_base"\<close>
      and path = \<open>FI.long_name\<close>
      and more_args = \<open>
        structure Log = Logging.EResolve_Action_Data
        structure TI = Discrimination_Tree\<close>\<close>
    val key_of_thm = Thm.major_prem_of\<close>\<close>

\<^functor_instance>\<open>struct_name = DResolve
  and functor_name = Zippy_Resolve_Action_Data_Mixin
  and id = \<open>FI.prefix_id "zauto_dresolve_action_data"\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    structure Res_AC_Data = \<^functor_instance>\<open>functor_name = Zippy_Resolve_Action_Data_Mixin_Base
      and id = \<open>FI.prefix_id "zauto_dresolve_action_data_base"\<close>
      and path = \<open>FI.long_name\<close>
      and more_args = \<open>
        structure Log = Logging.DResolve_Action_Data
        structure TI = Discrimination_Tree\<close>\<close>
    val key_of_thm = Thm.major_prem_of\<close>\<close>
end
\<close>
(*reset grounding*)
setup\<open>Context.theory_map (ML_Gen.setup_zipper_args' (NONE, NONE) (NONE, NONE))\<close>

ML\<open>
\<^functor_instance>\<open>struct_name = Standard_Zippy_Auto
  and functor_name = Zippy_Auto
  and id = \<open>""\<close>\<close>
\<close>
local_setup\<open>Standard_Zippy_Auto.Init_AC_Data.setup_attribute NONE\<close>
local_setup\<open>Standard_Zippy_Auto.Resolve_Unif.Thm_Data.setup_attribute NONE\<close>
local_setup\<open>Standard_Zippy_Auto.Resolve_Match.Thm_Data.setup_attribute NONE\<close>
(* local_setup \<open>Standard_Zippy_Auto.EResolve.setup_attribute NONE\<close> *)
(* local_setup \<open>Standard_Zippy_Auto.DResolve.setup_attribute NONE\<close> *)

declare [[zauto_init_ac add = \<open>
  let
    open Zippy Standard_Zippy_Auto.Resolve_Unif; open MU.SC
    val cons_resolve = Tac_Util.cons_resolve_ho_unif_first_action_cluster
    fun lookup ctxt = snd #> Data.TI.norm_term
      #> Data.TI.unifiables (Data.get_index (Context.Proof ctxt))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
      (init_focused_goals_none_all_data (lookup ctxt) goals #> cons_resolve) focus)
      >>> Up3.morph
  in (@{binding resolve_ho_unif_first}, init_ac) end
\<close>]]
and [[zauto_init_ac add = \<open>
  let
    open Zippy Standard_Zippy_Auto.Resolve_Match; open MU.SC
    val cons_resolve = Tac_Util.cons_resolve_ho_match_first_action_cluster
    fun lookup ctxt = snd #> Data.TI.norm_term
      #> Data.TI.unifiables (Data.get_index (Context.Proof ctxt))
    fun init_ac (_, goals) focus = Ctxt.with_ctxt (fn ctxt =>
      (init_focused_goals_none_all_data (lookup ctxt) goals #> cons_resolve) focus)
      >>> Up3.morph
  in (@{binding resolve_ho_match_first}, init_ac) end
\<close>]]

ML\<open>
local open Zippy Standard_Zippy_Auto; open MU.Mo
in
fun init_action_clusters focus z = Ctxt.get_ctxt () >>= (fn ctxt =>
  let
    val state = Mixin2.GCluster.get_state z
    val goals = Thm.prems_of state |> List.map (Term_Util.strip_subgoal #> snd)
    fun init_with_args init = init (state, goals) focus
    val init = Init_AC_Data.get_table (Context.Proof ctxt)
      |> Init_AC_Data.Table.dest
      |> ZB.LF.foldlM (snd #> init_with_args)
  in init z end)
end
\<close>

ML\<open>
local open Zippy Standard_Zippy_Auto; open MU; open Mo SC A
in
  fun resolve_action_data {updates, mk_cud, prio_sq_co, progress} thm context =
    let
      val nupdates = length updates
      val nprems = Thm.nprems_of thm
      val ctxt = Context.proof_of context
    in
      if nupdates = nprems
      then
        {thm = thm,
        updates = updates,
        mk_cud = mk_cud,
        progress = progress,
        prio_sq_co = prio_sq_co}
      else error (Pretty.breaks [
          Pretty.block [Pretty.str "Number of updates ",
            Pretty.enclose "(" ")" [SpecCheck_Show.int nupdates]],
          Pretty.block [Pretty.str "does not match number of premises ",
            Pretty.enclose "(" ")." [SpecCheck_Show.int nprems]],
          Pretty.block [Pretty.str "of theorem ", Thm.pretty_thm ctxt thm]
        ] |> Pretty.block |> Pretty.string_of)
    end
  fun foo {prio, updates, progress} =
    resolve_action_data
      {updates = updates,
      mk_cud = Util.copy_update_data_empty_changed,
      progress = progress,
      prio_sq_co = Tac_Util.enum_halve_prio_halve_prio_depth_sq_co prio}
end
\<close>

(* declare[[ML_map_context \<open>Logger.set_log_levels Logger.root Logger.ALL\<close>]] *)
declare conjI[zauto_resolve_match_action_data_thm_data add = \<open>foo {prio = Prio.VERY_HIGH,
  updates = [Zippy.Tac.GPU.F.single #> init_action_clusters, Zippy.Tac.GPU.F.single #> init_action_clusters],
  progress = Zippy.Mixin5.Meta.Meta.P.promising}
\<close>]
(* declare TrueI[zauto_resolve_unif_action_data_thm_data add = \<open>foo {prio = Prio.VERY_HIGH,
  updates = [],
  progress = Zippy.Mixin5.Meta.Meta.P.promising}\<close>] *)
declare disjI1[zauto_resolve_match_action_data_thm_data add = \<open>foo {prio = Prio.VERY_HIGH,
  updates = [Zippy.Tac.GPU.F.single #> init_action_clusters],
  progress = Zippy.Mixin5.Meta.Meta.P.promising}\<close>]
declare disjI2[zauto_resolve_match_action_data_thm_data add = \<open>foo {prio = Prio.VERY_HIGH,
  updates = [Zippy.Tac.GPU.F.single #> init_action_clusters],
  progress = Zippy.Mixin5.Meta.Meta.P.promising}\<close>]

declare[[ML_print_depth=100]]
schematic_goal shows "?A \<and> True" "True \<and> ?A" "True \<and> False \<or> True"
(* supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.ALL\<close>]] *)
apply (tactic \<open>fn state =>
  let
    open Zippy; open MU; open Mo SC
    fun run _ =
      (*initialise the zipper*)
      (Util.init_thm_state state
      (*add actions*)
      >>= Down1.morph
      >>= init_action_clusters (Tac.GPU.F.Goals [1,2])
      >>= Z2.ZM.Down.morph
      >>= init_action_clusters Tac.GPU.F.none
      >>= ZB.top2
      >>= Z1.ZM.Unzip.morph
      (*run best-first-search*)
      >>= Run.init_repeat_step_queue
        (Ctxt.with_ctxt Run.mk_df_post_unreturned_unfinished_statesq) (SOME 1000)
      )
      |> Run.seq_from_monad {ctxt = @{context}, state = ()}
      |> Seq.map (Run.get_result_data #> #thm_states) |> Seq.flat |> Tactic_Util.unique_thmsq
      |> Seq.pull |> Library.K |> Seq.make
      (* |> Seq.list_of |> Seq.of_list *)
    val (time, ressq) = Timing.timing run () |> apfst @{print}
  in ressq end
\<close>)
back
back
back
back
oops

end
