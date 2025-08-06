(*  Title:      Zippy/zippy_instance_resolve_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_RESOLVE_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_RESOLVE_DATA_ADD_ARGS
  [empty_action, default_update, updates, mk_cud, progress, prio_sq_co]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_RESOLVE_DATA_CONFIG_ARGS
  [empty_action, default_update, mk_cud, progress, prio_sq_co, del_select]}

signature ZIPPY_INSTANCE_RESOLVE_DATA_ARGS =
sig
  structure PM : PARSE_ZIPPY_INSTANCE_RESOLVE_DATA_MODE
  structure PAA : PARSE_ZIPPY_INSTANCE_RESOLVE_DATA_ADD_ARGS
  structure PCA : PARSE_ZIPPY_INSTANCE_RESOLVE_DATA_CONFIG_ARGS

  val PAA_entries_from_PCA_entries : ('a, 'b, 'c, 'd, 'e, 'f) PCA.entries -> 'u option ->
    ('a, 'b, 'u, 'c, 'd, 'e) PAA.entries

  val add_arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    (int * ML_Code_Util.code) list parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser) PAA.entries
  val del_arg_parser : ML_Code_Util.code parser
  val config_arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser) PCA.entries
end

structure Zippy_Instance_Resolve_Data_Args : ZIPPY_INSTANCE_RESOLVE_DATA_ARGS =
struct

structure PU = Parse_Util

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PAA [empty_action, default_update, updates, mk_cud, progress, prio_sq_co]}
@{parse_entries (struct) PDA [select]}
@{parse_entries (struct) PCA [empty_action, default_update, mk_cud, progress, prio_sq_co, del_select]}

fun PAA_entries_from_PCA_entries {empty_action, default_update, mk_cud, progress, prio_sq_co,...}
  updates = {
  empty_action = empty_action, default_update = default_update, mk_cud = mk_cud,
  progress = progress, prio_sq_co = prio_sq_co, updates = updates}

val empty_action_parser = PU.nonempty_code (K "action in case of empty results must not be empty")
val default_update_parser = PU.nonempty_code (K "default update must not be empty")
val update_parser = PU.nonempty_code (K "update must not be empty")
val update_key_parser = PU.filter (curry (op <=) 0) (PU.fail (K "index must be greater than 0"))
  Parse.nat
val opt_updates_parser = Parse.list (Parse.underscore >> K NONE || update_parser >> SOME)
val key_updates_parser =
  PU.distinct_list (eq_fst (op =)) (K (K "updates must not contain duplicate keys"))
  (Parse.list (update_key_parser --| Parse.$$$ ":" -- update_parser))
val updates_parser = (Parse.$$$ "["
  |-- (PU.nonempty_list (K "") key_updates_parser
  || opt_updates_parser >>
    (tag_list 1 #> map_filter (fn (_, NONE) => NONE | (i, SOME x) => SOME (i, x))))
  --| Parse.$$$ "]")

val mk_cud_parser = PU.nonempty_code (K "copy update data function must not be empty")
val prio_sq_co_parser = PU.nonempty_code (K "priority result sequence coroutine must not be empty")
val progress_parser = PU.nonempty_code (K "progress must not be empty")

val add_arg_parsers = {
  empty_action = SOME empty_action_parser,
  default_update = SOME default_update_parser,
  updates = SOME updates_parser,
  mk_cud = SOME mk_cud_parser,
  prio_sq_co = SOME prio_sq_co_parser,
  progress = SOME progress_parser
}

val del_arg_parser = PU.nonempty_code (K "deletion selector must not be empty")

val config_arg_parsers = {
  empty_action = SOME empty_action_parser,
  default_update = SOME default_update_parser,
  mk_cud = SOME mk_cud_parser,
  prio_sq_co = SOME prio_sq_co_parser,
  progress = SOME progress_parser,
  del_select = SOME del_arg_parser
}
end

signature ZIPPY_INSTANCE_RESOLVE_DATA =
sig
  include ZIPPY_INSTANCE_RESOLVE

  structure Resolve_Data :
  sig
    structure Data : GENERIC_TERM_INDEX_DATA
    where type value = @{AllT_args} Resolve.data

    val init_focused_goals_none_all_data : ('a -> Data.term_value list) -> 'a list ->
      Base_Data.GFocus.focus -> (Base_Data.GFocus.focus * Data.value) list
    val init_focused_goals_none_no_data : ('a -> Data.term_value list) -> 'a list ->
      Base_Data.GFocus.focus -> (Base_Data.GFocus.focus * Data.value) list

    type config_args = (@{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph,
      @{AllT_args} Result_Action.mk_copy_update_data,
      Base_Data.AAMeta.P.progress,
      @{AllT_args} PResults.prio_sq_co,
      Data.term_value -> bool) Zippy_Instance_Resolve_Data_Args.PCA.entries

    structure Config_Data : GENERIC_DATA
    where type T = config_args

    val get_config_args : Context.generic -> Config_Data.T
    val map_config_args : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

    val get_empty_action : Context.generic -> @{AllT_args} Base_Data.PAction.action
    val map_empty_action :
      (@{AllT_args} Base_Data.PAction.action -> @{AllT_args} Base_Data.PAction.action) ->
      Context.generic -> Context.generic

    val get_default_update : Context.generic -> Base_Data.GCS.goal_pos ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph
    val map_default_update :
      ((Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph) ->
        Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph) ->
      Context.generic -> Context.generic

    val get_mk_cud : Context.generic -> @{AllT_args} Result_Action.mk_copy_update_data
    val map_mk_cud : (@{AllT_args} Result_Action.mk_copy_update_data ->
      @{AllT_args} Result_Action.mk_copy_update_data) -> Context.generic -> Context.generic

    val get_progress : Context.generic -> Base_Data.AAMeta.P.progress
    val map_progress : (Base_Data.AAMeta.P.progress -> Base_Data.AAMeta.P.progress) ->
      Context.generic -> Context.generic

    val get_prio_sq_co : Context.generic -> @{AllT_args} PResults.prio_sq_co
    val map_prio_sq_co : (@{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co) -> Context.generic -> Context.generic

    val get_del_select : Context.generic -> Data.term_value -> bool
    val map_del_select : ((Data.term_value -> bool) -> Data.term_value -> bool) ->
      Context.generic -> Context.generic

    type add_args = (@{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph,
      (int * (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph)) list,
      @{AllT_args} Result_Action.mk_copy_update_data,
      Base_Data.AAMeta.P.progress,
      @{AllT_args} PResults.prio_sq_co) Zippy_Instance_Resolve_Data_Args.PAA.entries

    val insert : Data.value -> Context.generic -> Context.generic
    val insert_args : add_args -> thm -> Context.generic -> Context.generic
    val insert_args_context_defaults : add_args -> thm -> Context.generic -> Context.generic

    val delete : (Data.term_value -> bool) -> thm -> Context.generic -> Context.generic
    val delete_context_defaults : (Data.term_value -> bool) option -> thm -> Context.generic ->
      Context.generic

    val binding : Binding.binding
    val parse_add_arg_entries : (ML_Code_Util.code, ML_Code_Util.code,
      (int * ML_Code_Util.code) list, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
      Zippy_Instance_Resolve_Data_Args.PAA.entries parser
    val add_attribute : (ML_Code_Util.code, ML_Code_Util.code, (int * ML_Code_Util.code) list,
        ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
        Zippy_Instance_Resolve_Data_Args.PAA.entries * Position.T ->
      attribute

    val del_attribute : ML_Code_Util.code option * Position.T -> attribute

    val parse_config_arg_entries : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
      Zippy_Instance_Resolve_Data_Args.PCA.entries parser
    val config_attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
        ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
        Zippy_Instance_Resolve_Data_Args.PCA.entries * Position.T ->
      attribute

    val parse_attribute : attribute parser
    val setup_attribute : string option -> local_theory -> local_theory
  end
end

functor Zippy_Instance_Resolve_Data(
    structure FI_Resolve_Data : FUNCTOR_INSTANCE_BASE (*target structure for Resolve_Data*)
    structure Z : ZIPPY_INSTANCE_RESOLVE
    structure TI : TERM_INDEX
    val key_of_thm : thm -> term
    val num_new_goals : thm -> int
    val init_args : (@{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLP.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      Z.Base_Data.AAMeta.P.progress,
      @{AllT_args} Z.PResults.prio_sq_co,
      term * @{AllT_args} Z.Resolve.data -> bool)
      Zippy_Instance_Resolve_Data_Args.PCA.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_RESOLVE_DATA =
struct
open Z; open ZLP
structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util

structure Resolve_Data =
struct
structure FI = Functor_Instance(FI_Resolve_Data)
\<^functor_instance>\<open>struct_name: Data
  functor_name: Generic_Term_Index_Data
  id: \<open>FI.prefix_id "data"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Log.logger
    structure TI = TI
    type value = @{AllT_args} Z.Resolve.data
    val eq_value = Z.Resolve.eq_data
    val pretty_value = Z.Resolve.pretty_data\<close>\<close>

local open Zippy_Instance_Resolve_Data_Args Base_Data
in
fun gen_init_focused_goals_data focused_goals lookup x focus = focused_goals focus x
  |> maps (apsnd lookup #> (fn (i, datas) => List.map (snd #> pair (GFocus.single i)) datas))
fun init_focused_goals_none_all_data x = gen_init_focused_goals_data GFocus.focused_goals_none_all x
fun init_focused_goals_none_no_data x = gen_init_focused_goals_data GFocus.focused_goals_none_no x

type config_args = (@{AllT_args} PAction.action,
  GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph,
  @{AllT_args} Result_Action.mk_copy_update_data,
  AAMeta.P.progress,
  @{AllT_args} PResults.prio_sq_co,
  Data.term_value -> bool) PCA.entries

structure Config_Data = Generic_Data(
  type T = config_args
  val empty = init_args
  val merge = fst)

val get_config_args = Config_Data.get
val map_config_args = Config_Data.map

val get_empty_action = PCA.get_empty_action o get_config_args
val map_empty_action = map_config_args o PCA.map_empty_action

val get_default_update = PCA.get_default_update o get_config_args
val map_default_update = map_config_args o PCA.map_default_update

val get_mk_cud = PCA.get_mk_cud o get_config_args
val map_mk_cud = map_config_args o PCA.map_mk_cud

val get_progress = PCA.get_progress o get_config_args
val map_progress = map_config_args o PCA.map_progress

val get_prio_sq_co = PCA.get_prio_sq_co o get_config_args
val map_prio_sq_co = map_config_args o PCA.map_prio_sq_co

val get_del_select = PCA.get_del_select o get_config_args
val map_del_select = map_config_args o PCA.map_del_select

type add_args = (@{AllT_args} PAction.action,
  GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph,
  (int * (GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph)) list,
  @{AllT_args} Result_Action.mk_copy_update_data,
  AAMeta.P.progress,
  @{AllT_args} PResults.prio_sq_co) PAA.entries

fun insert {empty_action, thm, updates, mk_cud, progress, prio_sq_co} context =
  let
    val thm = Thm.trim_context thm
    val num_new_goals = num_new_goals thm
    val nupdates = length updates
  in
    if num_new_goals <> nupdates
    then error (Pretty.breaks [
        Pretty.block [Pretty.str "Number of updates ",
          Pretty.enclose "(" ")" [SpecCheck_Show.int nupdates]],
        Pretty.block [Pretty.str "does not match number of new goals ",
          Pretty.enclose "(" ")" [SpecCheck_Show.int num_new_goals]],
        Pretty.block [Pretty.str "of theorem ", Thm.pretty_thm (Context.proof_of context) thm]
      ] |> Pretty.block |> Pretty.string_of)
    else Data.insert (key_of_thm thm, {empty_action = empty_action, thm = thm, updates = updates,
      mk_cud = mk_cud, progress = progress, prio_sq_co = prio_sq_co}) context
  end

fun insert_args entries thm context =
  let
    val num_new_goals = num_new_goals thm
    val default_update = PAA.get_default_update entries
    fun mk_updates i [] = if i <= num_new_goals + 1
          then replicate (num_new_goals + 1 - i) default_update
          else error (Pretty.breaks [
              Pretty.block [Pretty.str "Too many updates ",
                Pretty.enclose "(" ")." [SpecCheck_Show.int (i - 1)]],
              Pretty.block [Pretty.str "Theorem ", Thm.pretty_thm (Context.proof_of context) thm,
                Pretty.str " creates only ",
                Pretty.enclose "(" ")" [SpecCheck_Show.int num_new_goals],
                Pretty.str " new goals."]
            ] |> Pretty.block |> Pretty.string_of)
      | mk_updates i (ups as ((j, update) :: updates))= if i < j
          then default_update :: mk_updates (i + 1) ups
          else if i = j then update :: mk_updates (i + 1) updates
          else error (Pretty.block [
              Pretty.str "Invalid update indices (non-positive or duplicates)."
            ] |> Pretty.string_of)
    val updates = PAA.get_updates entries |> sort (apply2 fst #> int_ord) |> mk_updates 1
  in
    insert {empty_action = PAA.get_empty_action entries, thm = thm, updates = updates,
      mk_cud = PAA.get_mk_cud entries, progress = PAA.get_progress entries,
      prio_sq_co = PAA.get_prio_sq_co entries} context
  end

fun insert_args_context_defaults entries thm context =
  let
    val default_entries = PAA_entries_from_PCA_entries (get_config_args context) NONE
    val entries = PAA.merge_entries entries default_entries
  in insert_args entries thm context end

fun delete select thm = Data.delete (key_of_thm thm, select)
fun delete_context_defaults opt_select thm context =
  let val select = case opt_select of SOME sel => sel | NONE => get_del_select context
  in Data.delete (key_of_thm thm, select) context end

val binding = Binding.make (FI.id, FI.pos)

val add_default_entries = PAA.empty_entries () |> fold PAA.set_entry [PAA.updates []]

val parse_add_arg_entries =
  let
    val parsers = add_arg_parsers
    val parse_value = PAA.parse_entry (PAA.get_empty_action parsers)
      (PAA.get_default_update parsers) (PAA.get_updates parsers)
      (PAA.get_mk_cud parsers) (PAA.get_progress parsers) (PAA.get_prio_sq_co parsers)
    val parse_entry = Parse_Key_Value.parse_entry PAA.parse_key (K PU.eq) parse_value
  in PAA.parse_entries_required Scan.repeat1 [] parse_entry add_default_entries end

fun ZRDArgs_substructure_op substructure operation =
  MCU.flat_read ["Zippy_Instance_Resolve_Data_Args.", substructure, ".", operation]

fun add_attribute (entries, pos) =
  let
    val code_PAA_op = ZRDArgs_substructure_op "PAA"
    val code_from_key = code_PAA_op o PAA.key_to_string
    fun code_from_entry (PAA.empty_action c) = c
      | code_from_entry (PAA.default_update c) = c
      | code_from_entry (PAA.updates updates) = updates
          |> List.map (fn (i, update) => MCU.tuple [MCU.read (string_of_int i), update])
          |> MCU.list
      | code_from_entry (PAA.mk_cud c) = c
      | code_from_entry (PAA.progress c) = c
      | code_from_entry (PAA.prio_sq_co c) = c
    val code_entries = PAA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code = FI.code_struct_op "insert_args_context_defaults" @
      MCU.atomic (code_PAA_op "entries_from_entry_list" @ code_entries)
  in ML_Attribute.run_declaration_attribute (code, pos) end

fun del_attribute (NONE, _) = Thm.declaration_attribute (delete_context_defaults NONE)
  | del_attribute (SOME select, pos) =
  let val code = FI.code_struct_op "delete_context_defaults" @ MCU.atomic select
  in ML_Attribute.run_declaration_attribute (code, pos) end

val parse_config_arg_entries =
  let
    val parsers = config_arg_parsers
    val parse_value = PCA.parse_entry (PCA.get_empty_action parsers)
      (PCA.get_default_update parsers) (PCA.get_mk_cud parsers) (PCA.get_progress parsers)
      (PCA.get_prio_sq_co parsers) (PCA.get_del_select parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key (K PU.eq) parse_value
    val default_entries = PCA.empty_entries ()
  in PCA.parse_entries_required Scan.repeat1 [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val code_PCA_op = ZRDArgs_substructure_op "PCA"
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.empty_action c) = c
      | code_from_entry (PCA.default_update c) = c
      | code_from_entry (PCA.mk_cud c) = c
      | code_from_entry (PCA.progress c) = c
      | code_from_entry (PCA.prio_sq_co c) = c
      | code_from_entry (PCA.del_select c) = c
    val code_entries = PCA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_config_args" @ MCU.atomic (code_PCA_op "merge_entries" @
      MCU.atomic (code_PCA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parse_value = PM.parse_entry parse_add_arg_entries (Scan.option del_arg_parser)
      parse_config_arg_entries
    val parse_entry = Parse_Key_Value.parse_entry PM.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PM.empty_entries ()
  in PM.parse_entries_required Scan.repeat1 [] parse_entry default_entries end

fun attribute (entries, pos) =
  let
    fun default_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PM.get_add_safe entries
      |> (fn SOME entries => add_attribute (entries, pos) | NONE => default_attr)
    val del_attr = PM.get_del_safe entries
      |> (fn SOME entries => del_attribute (entries, pos) | NONE => default_attr)
    val config_attr = PM.get_config_safe entries
      |> (fn SOME entries => config_attribute (entries, pos) | NONE => default_attr)
  in AU.apply_attribute config_attr #> AU.apply_attribute del_attr #> add_attr end

val parse_attribute = PU.position parse_entries >> attribute
  || PU.position parse_add_arg_entries >> add_attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("add/del resolve data " ^ enclose "(" ")" FI.long_name)
end
end
end
