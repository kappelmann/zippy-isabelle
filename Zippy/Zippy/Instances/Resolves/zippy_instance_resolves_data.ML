(*  Title:      Zippy/zippy_instance_resolves_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_RESOLVES_DATA_MODES [match, unif]}

signature ZIPPY_INSTANCE_RESOLVES_DATA_ARGS =
sig
  structure PM : PARSE_ZIPPY_INSTANCE_RESOLVES_DATA_MODES
  type mode = PM.key
  val parse_mode : mode parser
end

structure Zippy_Instance_Resolves_Data_Args : ZIPPY_INSTANCE_RESOLVES_DATA_ARGS =
struct

@{parse_entries (struct) PM [match, unif]}
type mode = PM.key
val parse_mode = PM.parse_key
end

functor Zippy_Instance_Resolves_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure TI : TERM_INDEX
    val init_args : (Z.Base_Data.AAMeta.P.progress,
      int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLP.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      @{AllT_args} Z.PResults.prio_sq_co,
      thm * (term * (thm,
        Z.Base_Data.AAMeta.P.progress,
        int -> @{AllT_args} Z.Base_Data.PAction.action,
        (Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLP.Z2.zipper) Z.emorph) list,
        @{AllT_args} Z.Result_Action.mk_copy_update_data,
        @{AllT_args} Z.PResults.prio_sq_co)
        Zippy_Instance_Hom_Changed_Goals_Data_Args.PD.entries) -> bool)
        Zippy_Instance_Hom_Changed_Goals_Data_Args.PDC.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) =
struct
local structure FI =  Functor_Instance(FI)
in
structure Logging =
struct
  local structure Base = struct val parent_logger = Log.logger end
  in
  structure Resolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve_Unif")
  structure Resolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve_Match")
  structure EResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve_Unif")
  structure EResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve_Match")
  structure DResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve_Unif")
  structure DResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve_Match")
  structure FResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve_Unif")
  structure FResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve_Match")
  end
end

local open Z; open ZLP
  structure Base = struct structure Z = Z; structure TI = TI; val init_args = init_args end
in
\<^functor_instance>\<open>struct_name: Resolve_Unif
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "resolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.Resolve_Unif\<close>\<close>
structure Resolve_Unif = Resolve_Unif.Hom_Changed_Goals_Data
\<^functor_instance>\<open>struct_name: Resolve_Match
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "resolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.Resolve_Match\<close>\<close>
structure Resolve_Match = Resolve_Match.Hom_Changed_Goals_Data

\<^functor_instance>\<open>struct_name: EResolve_Unif
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "eresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    structure Log = Logging.EResolve_Unif\<close>\<close>
structure EResolve_Unif = EResolve_Unif.Hom_Changed_Goals_Data
\<^functor_instance>\<open>struct_name: EResolve_Match
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "eresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    structure Log = Logging.EResolve_Match\<close>\<close>
structure EResolve_Match = EResolve_Match.Hom_Changed_Goals_Data

\<^functor_instance>\<open>struct_name: DResolve_Unif
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "dresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.DResolve_Unif\<close>\<close>
structure DResolve_Unif = DResolve_Unif.Hom_Changed_Goals_Data
\<^functor_instance>\<open>struct_name: DResolve_Match
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "dresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.DResolve_Match\<close>\<close>
structure DResolve_Match = DResolve_Match.Hom_Changed_Goals_Data

\<^functor_instance>\<open>struct_name: FResolve_Unif
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "fresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.FResolve_Unif\<close>\<close>
structure FResolve_Unif = FResolve_Unif.Hom_Changed_Goals_Data
\<^functor_instance>\<open>struct_name: FResolve_Match
  functor_name: Zippy_Instance_Hom_Changed_Goals_Data
  FI_struct_name: FI_Hom_Changed_Goals_Data
  id: \<open>FI.prefix_id "fresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.FResolve_Match\<close>\<close>
structure FResolve_Match = FResolve_Match.Hom_Changed_Goals_Data

local
  open Zippy_Instance_Resolves_Data_Args
  structure PMD = Zippy_Instance_Hom_Changed_Goals_Data_Args.PM
  val parse_mode_opt_default = Scan.optional (Args.parens (Parse.!!! PM.parse_key)) (PM.key PM.unif)
  fun gen_parse_attribute match unif = parse_mode_opt_default
    :|-- (fn PM.match _ => match | PM.unif _ => unif)
  fun gen_setup_attribute binding what parse_attribute = Attrib.local_setup binding
    (Parse.!!! parse_attribute |> Scan.lift) o
    the_default ("configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name)
  fun gen_parse_method match unif =
    let val parse = Scan.lift parse_mode_opt_default
      :|-- (fn PM.match _ => match | PM.unif _ => unif)
    in Parse.and_list1' parse >> K () end
in
val parse_resolve_attribute = gen_parse_attribute
  Resolve_Match.parse_attribute Resolve_Unif.parse_attribute
val parse_eresolve_attribute = gen_parse_attribute
  EResolve_Match.parse_attribute EResolve_Unif.parse_attribute
val parse_dresolve_attribute = gen_parse_attribute
  DResolve_Match.parse_attribute DResolve_Unif.parse_attribute
val parse_fresolve_attribute = gen_parse_attribute
  FResolve_Match.parse_attribute FResolve_Unif.parse_attribute

val resolve_binding = Binding.make (FI.prefix_id "resolve", FI.pos)
val eresolve_binding = Binding.make (FI.prefix_id "eresolve", FI.pos)
val dresolve_binding = Binding.make (FI.prefix_id "dresolve", FI.pos)
val fresolve_binding = Binding.make (FI.prefix_id "fresolve", FI.pos)

val setup_resolve_attribute = gen_setup_attribute
  resolve_binding "resolution" parse_resolve_attribute
val setup_eresolve_attribute = gen_setup_attribute
  eresolve_binding "e-resolution" parse_eresolve_attribute
val setup_dresolve_attribute = gen_setup_attribute
  dresolve_binding "d-resolution" parse_dresolve_attribute
val setup_fresolve_attribute = gen_setup_attribute
  fresolve_binding "f-resolution" parse_fresolve_attribute

val parse_resolve_method = gen_parse_method
  Resolve_Match.parse_entry_context_update Resolve_Unif.parse_entry_context_update
val parse_eresolve_method = gen_parse_method
  EResolve_Match.parse_entry_context_update EResolve_Unif.parse_entry_context_update
val parse_dresolve_method = gen_parse_method
  DResolve_Match.parse_entry_context_update DResolve_Unif.parse_entry_context_update
val parse_fresolve_method = gen_parse_method
  FResolve_Match.parse_entry_context_update FResolve_Unif.parse_entry_context_update
end
end
end
end
