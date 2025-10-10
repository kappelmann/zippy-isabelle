(*  Title:      Zippy/zippy_instance_cases_data.ML
    Author:     Kevin Kappelmann

Data for tactic actions creating a homogeneous number of changed goals for a given theorem.
*)
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA
  [insts, rule, simp, facts, match, progress, empty_action, updates, mk_cud, prio_sq_co]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA_OPT
  [rule, simp, facts, match, progress, empty_action, updates, mk_cud, prio_sq_co]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA_ADD_DEL_ARGS
  [insts, simp, facts, match, progress, empty_action, default_update, updates, mk_cud, prio_sq_co]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA_OPT_ADD_DEL_ARGS
  [simp, facts, match, progress, empty_action, default_update, updates, mk_cud, prio_sq_co]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA_CONFIG
  [simp, match, progress, empty_action, default_update, mk_cud, prio_sq_co, del_select]}
@{parse_entries (sig) PARSE_ZIPPY_INSTANCE_CASES_DATA_INSTS_MODE [fix, pat, pred]}

signature ZIPPY_INSTANCE_CASES_DATA_ARGS =
sig
  structure PM : PARSE_ZIPPY_INSTANCE_CASES_DATA_MODE
  structure PD : PARSE_ZIPPY_INSTANCE_CASES_DATA
  structure POD : PARSE_ZIPPY_INSTANCE_CASES_DATA_OPT
  structure PADA : PARSE_ZIPPY_INSTANCE_CASES_DATA_ADD_DEL_ARGS
  structure POADA : PARSE_ZIPPY_INSTANCE_CASES_DATA_OPT_ADD_DEL_ARGS
  structure PDC : PARSE_ZIPPY_INSTANCE_CASES_DATA_CONFIG
  structure PIM : PARSE_ZIPPY_INSTANCE_CASES_DATA_INSTS_MODE

  val PD_entries_from_POD_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) POD.entries -> 'j ->
    ('j, 'a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) PD.entries
  val POD_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) PD.entries ->
    ('b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) POD.entries
  val PADA_entries_from_POADA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) POADA.entries -> 'j ->
    ('j, 'a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) PADA.entries
  (* val POADA_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e) PD.entries -> ('c, 'd, 'e) POADA.entries *)
  (* val PADA_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e) PD.entries -> ('a, 'c, 'd, 'e) PADA.entries *)
  val PD_entries_from_PADA_entries : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) PADA.entries -> 'k ->
    ('a, 'k, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) PD.entries

  (* val PD_entries_from_PADA_entries : ('a, 'b, 'du, 'c, 'd, 'e) PADA.entries -> 'f ->
    ('f, 'a, 'b, 'c, 'd, 'e) PD.entries
  val PADA_entries_from_PDC_entries : ('a, 'b, 'c, 'd, 'e, 'f) PDC.entries -> 'u option ->
    ('a, 'b, 'c, 'u, 'd, 'e) PADA.entries *)

  type insts = (term option list, (term * term list) option list, (term -> bool) option list)
    PIM.entry
  val insts_ord : insts ord
  val pretty_insts : Proof.context -> insts -> Pretty.T

  type match = term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool
  (* type data = (insts, thm option, bool, thm list, match) PD.entries
  type add_del_args = (insts, bool, thm list, match) PADA.entries
  val data_ord : data ord
  val eq_data : data * data -> bool
  val pretty_data : Proof.context -> data -> Pretty.T
  val transfer_data : theory -> data -> data *)

  val updates_parser : (int * ML_Code_Util.code) list parser
  val add_arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, (int * ML_Code_Util.code) list parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser) PADA.entries
  val del_arg_parsers : (ML_Code_Util.code parser) PDA.entries
  val config_data_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser, ML_Code_Util.code parser, ML_Code_Util.code parser,
    ML_Code_Util.code parser) PDC.entries
end

structure Zippy_Instance_Cases_Data_Args : ZIPPY_INSTANCE_CASES_DATA_ARGS =
struct

structure PU = Parse_Util
structure Show = SpecCheck_Show

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PD
  [insts, rule, simp, facts, match, progress, empty_action, updates, mk_cud, prio_sq_co]}
@{parse_entries (struct) POD
  [rule, simp, facts, match, progress, empty_action, updates, mk_cud, prio_sq_co]}
@{parse_entries (struct) PADA
  [insts, simp, facts, match, progress, empty_action, default_update, updates, mk_cud, prio_sq_co]}
@{parse_entries (struct) POADA
  [simp, facts, match, progress, empty_action, default_update, updates, mk_cud, prio_sq_co]}
@{parse_entries (struct) PDC
  [simp, match, progress, empty_action, default_update, mk_cud, prio_sq_co, del_select]}
@{parse_entries (struct) PIM [fix, pat, pred]}

fun PD_entries_from_POD_entries {rule, simp, facts, match, progress, empty_action, updates, mk_cud,
  prio_sq_co} insts =
  {insts = SOME insts, rule = rule, simp = simp, facts = facts, match = match, progress = progress,
  empty_action = empty_action, updates = updates, mk_cud = mk_cud, prio_sq_co = prio_sq_co}
fun POD_entries_from_PD_entries {rule, simp, facts, match, progress, empty_action, updates, mk_cud,
  prio_sq_co,...} =
  {rule = rule, simp = simp, facts = facts, match = match, progress = progress,
  empty_action = empty_action, updates = updates, mk_cud = mk_cud, prio_sq_co = prio_sq_co}
(* fun POADA_entries_from_PD_entries {simp, facts, match,...} = *)
  (* {simp = simp, facts = facts, match = match} *)
fun PADA_entries_from_POADA_entries {simp, facts, match, progress, empty_action, default_update,
  updates, mk_cud, prio_sq_co} insts =
  {insts = SOME insts, simp = simp, facts = facts, match = match, progress = progress,
  empty_action = empty_action, default_update = default_update, updates = updates, mk_cud = mk_cud,
  prio_sq_co = prio_sq_co}
(* fun PADA_entries_from_PD_entries {insts, simp, facts, match,...} = *)
  (* {insts = insts, simp = simp, facts = facts, match = match} *)
fun PD_entries_from_PADA_entries {insts, simp, facts, match, progress, empty_action, default_update,
  updates, mk_cud, prio_sq_co,...} rule =
  {insts = insts, rule = SOME rule, simp = simp, facts = facts, match = match, progress = progress,
  empty_action = empty_action, default_update = default_update, updates = updates, mk_cud = mk_cud,
  prio_sq_co = prio_sq_co}

type insts = ((term -> bool) option list, (term * term list) option list, term option list)
  PIM.entry

fun are_term_variants tp =
  let
    val thy = Context.the_global_context ()
    fun match tp = Pattern.first_order_match thy tp (Vartab.empty, Vartab.empty)
  in can match tp andalso can match (swap tp) end

fun term_ord tp = if are_term_variants tp then EQUAL else Term_Ord.fast_term_ord tp
fun insts_ord (PIM.fix x, PIM.fix y) = list_ord (option_ord term_ord) (x, y)
  | insts_ord (PIM.fix _, _) = LESS
  | insts_ord (_, PIM.fix _) = GREATER
  | insts_ord (PIM.pat x, PIM.pat y) =
      list_ord (option_ord (prod_ord term_ord (list_ord term_ord))) (x, y)
  | insts_ord (PIM.pat _, _) = LESS
  | insts_ord (_, PIM.pat _) = GREATER
  | insts_ord (PIM.pred x, PIM.pred y) = list_ord (option_ord (K EQUAL)) (x, y)
fun pretty_insts _ (PIM.pred x) = Show.list (Show.option (K (Pretty.str "<predicate>"))) x
  | pretty_insts ctxt (PIM.pat x) =
      Show.list (Show.option (Show.zip (Show.term ctxt) (Show.list (Show.term ctxt)))) x
  | pretty_insts ctxt (PIM.fix x) = Show.list (Show.option (Show.term ctxt)) x

type match = term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool

val empty_action_parser = PU.nonempty_code (K "action in case of empty results must not be empty")
val default_update_parser = PU.nonempty_code (K "default update must not be empty")
val update_parser = PU.nonempty_code (K "update must not be empty")
val opt_update_parser = Parse.maybe update_parser
val opt_updates_parser = Parse.list opt_update_parser
val update_key_parser = PU.filter (curry (op <=) 0) (PU.fail (K "index must be greater than 0"))
  Parse.nat
val key_updates_parser =
  PU.distinct_list (eq_fst (op =)) (K (K "updates must not contain duplicate keys"))
  (Parse.list (update_key_parser --| Parse.$$$ ":" -- update_parser))
val updates_parser = Args.bracks (
  PU.nonempty_list (K "") key_updates_parser
  || (opt_updates_parser
    >> (tag_list 1 #> map_filter (fn (_, NONE) => NONE | (i, SOME x) => SOME (i, x)))))

val mk_cud_parser = PU.nonempty_code (K "copy update data function must not be empty")
val prio_sq_co_parser = PU.nonempty_code (K "priority result sequence coroutine must not be empty")
val progress_parser = PU.nonempty_code (K "progress must not be empty")

val add_arg_parsers = {
  progress = SOME progress_parser,
  empty_action = SOME empty_action_parser,
  default_update = SOME default_update_parser,
  updates = SOME updates_parser,
  mk_cud = SOME mk_cud_parser,
  prio_sq_co = SOME prio_sq_co_parser}

val del_select_parser = PU.nonempty_code (K "deletion selector must not be empty")
val del_arg_parsers = {select = SOME del_select_parser}

val config_data_parsers = {
  progress = SOME progress_parser,
  empty_action = SOME empty_action_parser,
  default_update = SOME default_update_parser,
  mk_cud = SOME mk_cud_parser,
  prio_sq_co = SOME prio_sq_co_parser,
  del_select = SOME del_select_parser}
end

signature ZIPPY_INSTANCE_CASES_DATA =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure Hom_Changed_Goals_Data :
  sig
    type data = (thm,
      Base_Data.AAMeta.P.progress,
      int -> @{AllT_args} Base_Data.PAction.action,
      (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph) list,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.prio_sq_co) Zippy_Instance_Cases_Data_Args.PD.entries

    val transfer_data : theory -> data -> data

    structure Data : GENERIC_TERM_INDEX_DATA
    where type value = data

    type config = (Base_Data.AAMeta.P.progress,
      int -> @{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.prio_sq_co,
      thm * Data.term_value -> bool) Zippy_Instance_Cases_Data_Args.PDC.entries

    structure Config_Data : GENERIC_DATA
    where type T = config

    val get_config : Context.generic -> Config_Data.T
    val map_config : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

    val get_progress : Context.generic -> Base_Data.AAMeta.P.progress
    val map_progress : (Base_Data.AAMeta.P.progress -> Base_Data.AAMeta.P.progress) ->
      Context.generic -> Context.generic

    val get_empty_action : Context.generic -> int -> @{AllT_args} Base_Data.PAction.action
    val map_empty_action : ((int -> @{AllT_args} Base_Data.PAction.action) ->
        int -> @{AllT_args} Base_Data.PAction.action) ->
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

    val get_prio_sq_co : Context.generic -> @{AllT_args} PResults.prio_sq_co
    val map_prio_sq_co : (@{AllT_args} PResults.prio_sq_co ->
      @{AllT_args} PResults.prio_sq_co) -> Context.generic -> Context.generic

    val get_del_select : Context.generic -> thm * Data.term_value -> bool
    val map_del_select : ((thm * Data.term_value -> bool) -> thm * Data.term_value -> bool) ->
      Context.generic -> Context.generic

    type add_args = (Base_Data.AAMeta.P.progress,
      int -> @{AllT_args} Base_Data.PAction.action,
      Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph,
      (int * (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper) emorph)) list,
      @{AllT_args} Result_Action.mk_copy_update_data,
      @{AllT_args} PResults.prio_sq_co) Zippy_Instance_Cases_Data_Args.PADA.entries

    val insert : Data.value -> Context.generic -> Context.generic
    val insert_add_args : add_args -> thm -> Context.generic -> Context.generic
    val insert_add_args_context_defaults : add_args -> thm -> Context.generic -> Context.generic

    val delete : (thm * Data.term_value -> bool) -> thm -> Context.generic -> Context.generic
    val delete_context_defaults : (thm * Data.term_value -> bool) option -> thm ->
      Context.generic -> Context.generic

    val binding : Binding.binding
    val parse_add_arg_entries : (ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, (int * ML_Code_Util.code) list, ML_Code_Util.code, ML_Code_Util.code)
      Zippy_Instance_Cases_Data_Args.PADA.entries parser
    val add_attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
        (int * ML_Code_Util.code) list, ML_Code_Util.code, ML_Code_Util.code)
        Zippy_Instance_Cases_Data_Args.PADA.entries * Position.T ->
      attribute

    val parse_del_arg : ML_Code_Util.code option parser
    val del_attribute : ML_Code_Util.code option * Position.T -> attribute

    val parse_config_arg_entries : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
      ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
      Zippy_Instance_Cases_Data_Args.PDC.entries parser
    val config_attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code,
        ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
        Zippy_Instance_Cases_Data_Args.PDC.entries * Position.T ->
      attribute

    val parse_attribute : attribute parser
    val setup_attribute : (string, string) Either.either -> local_theory -> local_theory

    val parse_add_context_update : unit context_parser
    val parse_del_context_update : unit context_parser
    val parse_config_context_update : unit context_parser

    (* action data *)
    val focused_data_none_each : ('a -> Data.term_value list) -> 'a list ->
      Base_Data.GFocus.focus -> (Base_Data.GFocus.focus * Data.value) list
    val focused_data_none_no : ('a -> Data.term_value list) -> 'a list ->
      Base_Data.GFocus.focus -> (Base_Data.GFocus.focus * Data.value) list

    val tac_data_from_data : Base_Data.AMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      data -> @{AllT_args} Tac.data

    val paction_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
      Base_Data.AMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      data -> @{AllT_args} PAction.data

    val cons_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.AMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      data -> Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLP.Z3.zipper,
        @{AllT_args} ZLP.Z4.zipper) morph

    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.AAMeta.P.progress -> thm -> (@{ParaT_args} Base_Data.GFocus.focus,
        Tac_AAM.ztactic) morph) ->
      Proof.context -> (Base_Data.GFocus.focus * data) list ->
      (@{ParaT_args} @{AllT_args} ZLP.Z2.zipper, @{AllT_args} ZLP.Z3.zipper) morph
  end
end

functor Zippy_Instance_Cases_Data(
    structure FI_Hom_Changed_Goals_Data : FUNCTOR_INSTANCE_BASE (*target path for Hom_Changed_Goals_Data*)
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure TI : TERM_INDEX
    val key_of_thm : thm -> term
    val num_new_goals : thm -> int
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
        Zippy_Instance_Cases_Data_Args.PD.entries) -> bool)
        Zippy_Instance_Cases_Data_Args.PDC.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_CASES_DATA =
struct
open Z
structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util

structure Hom_Changed_Goals_Data =
struct
structure FI = Functor_Instance(FI_Hom_Changed_Goals_Data)

local open Zippy_Instance_Cases_Data_Args ZLP Base_Data
in
type data = (thm,
  AAMeta.P.progress,
  int -> @{AllT_args} PAction.action,
  (GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph) list,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.prio_sq_co) PD.entries

fun eq_data data = Thm.eq_thm (apply2 PD.get_thm data) andalso (op =) (apply2 PD.get_progress data)
fun pretty_data ctxt data = SpecCheck_Show.record [
    ("thm", Thm.pretty_thm ctxt (PD.get_thm data)),
    ("progress", Mixin5.Meta.Meta.P.pretty (PD.get_progress data))
  ]
fun transfer_data thy = PD.map_thm (Thm.transfer thy)

\<^functor_instance>\<open>struct_name: Data
  functor_name: Generic_Term_Index_Data
  id: \<open>FI.prefix_id "data"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Log.logger
    structure TI = TI
    type value = data
    val eq_value = eq_data
    val pretty_value = pretty_data\<close>\<close>

type config = (AAMeta.P.progress,
  int -> @{AllT_args} PAction.action,
  GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.prio_sq_co,
  thm * Data.term_value -> bool) PDC.entries

structure Config_Data = Generic_Data(
  type T = config
  val empty = init_args
  val merge = fst)

val get_config = Config_Data.get
val map_config = Config_Data.map

val get_progress = PDC.get_progress o get_config
val map_progress = map_config o PDC.map_progress

val get_empty_action = PDC.get_empty_action o get_config
val map_empty_action = map_config o PDC.map_empty_action

val get_default_update = PDC.get_default_update o get_config
val map_default_update = map_config o PDC.map_default_update

val get_mk_cud = PDC.get_mk_cud o get_config
val map_mk_cud = map_config o PDC.map_mk_cud

val get_prio_sq_co = PDC.get_prio_sq_co o get_config
val map_prio_sq_co = map_config o PDC.map_prio_sq_co

val get_del_select = PDC.get_del_select o get_config
val map_del_select = map_config o PDC.map_del_select

type add_args = (AAMeta.P.progress,
  int -> @{AllT_args} PAction.action,
  GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph,
  (int * (GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z2.zipper) emorph)) list,
  @{AllT_args} Result_Action.mk_copy_update_data,
  @{AllT_args} PResults.prio_sq_co) PADA.entries

fun insert data context =
  let
    val thm = Thm.trim_context (PD.get_thm data)
    val num_new_goals = num_new_goals thm
    val nupdates = length (PD.get_updates data)
  in
    if num_new_goals <> nupdates
    then error (Pretty.breaks [
        Pretty.block [Pretty.str "Number of updates ",
          Pretty.enclose "(" ")" [SpecCheck_Show.int nupdates]],
        Pretty.block [Pretty.str "does not match number of new goals ",
          Pretty.enclose "(" ")" [SpecCheck_Show.int num_new_goals]],
        Pretty.block [Pretty.str "for theorem ", Thm.pretty_thm (Context.proof_of context) thm]
      ] |> Pretty.block |> Pretty.string_of)
    else Data.insert (key_of_thm thm, PD.map_thm (K thm) data) context
  end

fun insert_add_args args thm context =
  let
    val num_new_goals = num_new_goals thm
    val default_update = PADA.get_default_update args
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
    val updates = PADA.get_updates args |> sort (apply2 fst #> int_ord) |> mk_updates 1
  in insert (PD_entries_from_PADA_entries (PADA.map_updates (K updates) args) thm) context end

fun insert_add_args_context_defaults entries thm context =
  let
    val default_entries = PADA_entries_from_PDC_entries (get_config context) NONE
    val entries = PADA.merge_entries entries default_entries
  in insert_add_args entries thm context end

fun delete select thm = Data.delete (key_of_thm thm, curry select thm)
fun delete_context_defaults opt_select thm context =
  let val select = case opt_select of SOME sel => sel | NONE => get_del_select context
  in delete select thm context end

val binding = Binding.make (FI.id, FI.pos)

val add_default_entries = PADA.empty_entries () |> fold PADA.set_entry [PADA.updates []]

val parse_add_arg_entry =
  let
    val parsers = add_arg_parsers
    val parse_value = PADA.parse_entry (PADA.get_progress parsers) (PADA.get_empty_action parsers)
      (PADA.get_default_update parsers) (PADA.get_updates parsers) (PADA.get_mk_cud parsers)
      (PADA.get_prio_sq_co parsers)
  in Parse_Key_Value.parse_entry PADA.parse_key (K (Parse.$$$ ":")) parse_value end

fun gen_parse_add_arg_entries repeat =
  PADA.parse_entries_required repeat true [] parse_add_arg_entry add_default_entries

val parse_add_arg_entries = gen_parse_add_arg_entries Scan.repeat

fun Args_substructure_op substructure operation =
  MCU.flat_read ["Zippy_Instance_Cases_Data_Args.", substructure, ".", operation]

fun add_attribute (entries, pos) =
  let
    val code_PADA_op = Args_substructure_op "PADA"
    val code_from_key = code_PADA_op o PADA.key_to_string
    fun code_from_entry (PADA.progress c) = c
      | code_from_entry (PADA.empty_action c) = c
      | code_from_entry (PADA.default_update c) = c
      | code_from_entry (PADA.updates updates) = updates
          |> List.map (fn (i, update) => MCU.tuple [MCU.read (string_of_int i), update])
          |> MCU.list
      | code_from_entry (PADA.mk_cud c) = c
      | code_from_entry (PADA.prio_sq_co c) = c
    val code_entries = PADA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code = FI.code_struct_op "insert_add_args_context_defaults" @
      MCU.atomic (code_PADA_op "entries_from_entry_list" @ code_entries)
  in ML_Attribute.run_declaration_attribute (code, pos) end

val parse_del_arg = PU.option (PDA.get_select del_arg_parsers)
val parse_del_arg_entry =
  let
    val parsers = del_arg_parsers
    val parse_value = PDA.parse_entry (PDA.get_select parsers)
  in Parse_Key_Value.parse_entry PDA.parse_key (K (Parse.$$$ ":")) parse_value end
fun parse_del_arg_entries repeat =
  PDA.parse_entries_required repeat true [] parse_del_arg_entry (PDA.empty_entries ())

fun del_attribute (NONE, _) = Thm.declaration_attribute (delete_context_defaults NONE)
  | del_attribute (SOME select, pos) =
  let val code = FI.code_struct_op "delete_context_defaults" @
    MCU.atomic (MCU.read "SOME" @ MCU.atomic select)
  in ML_Attribute.run_declaration_attribute (code, pos) end

val parse_config_arg_entries =
  let
    val parsers = config_data_parsers
    val parse_value = PDC.parse_entry (PDC.get_progress parsers) (PDC.get_empty_action parsers)
      (PDC.get_default_update parsers) (PDC.get_mk_cud parsers) (PDC.get_prio_sq_co parsers)
      (PDC.get_del_select parsers)
    val parse_entry = Parse_Key_Value.parse_entry PDC.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PDC.empty_entries ()
  in PDC.parse_entries_required Scan.repeat1 true [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val code_PDC_op = Args_substructure_op "PDC"
    val code_from_key = code_PDC_op o PDC.key_to_string
    fun code_from_entry (PDC.progress c) = c
      | code_from_entry (PDC.empty_action c) = c
      | code_from_entry (PDC.default_update c) = c
      | code_from_entry (PDC.mk_cud c) = c
      | code_from_entry (PDC.prio_sq_co c) = c
      | code_from_entry (PDC.del_select c) = c
    val code_entries = PDC.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_config" @ MCU.atomic (code_PDC_op "merge_entries" @
      MCU.atomic (code_PDC_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parse_value = PM.parse_entry parse_add_arg_entries parse_del_arg
      parse_config_arg_entries
    val parse_entry = Parse_Key_Value.parse_entry PM.parse_key (K (Scan.succeed "")) parse_value
  in PM.parse_entries_required Parse.and_list1 true [] parse_entry (PM.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun default_attr (context, thm) = (SOME context, SOME thm)
    val add_attr = PM.get_add_safe entries
      |> (fn SOME entries => add_attribute (entries, pos) | NONE => default_attr)
    val del_attr = PM.get_del_safe entries
      |> (fn SOME sel => del_attribute (sel, pos) | NONE => default_attr)
    val config_attr = PM.get_config_safe entries
      |> (fn SOME entries => config_attribute (entries, pos) | NONE => default_attr)
  in AU.apply_attribute config_attr #> AU.apply_attribute del_attr #> add_attr end

val parse_attribute = PU.position parse_entries >> attribute
  || PU.position parse_add_arg_entries >> add_attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  (Either.cases I (fn what => "configure " ^ what ^ " data " ^ enclose "(" ")" FI.long_name))

local
  fun parse_thms unless = Scan.repeats (Scan.unless (Scan.lift unless) Parse_Util.multi_thm)
    |> PU.nonempty_list (K "List of theorems must not be empty.")
  val parse_opt_sep = Scan.lift (Scan.option (Args.$$$ "use"))
  fun parse_run_attr (thms, attr) =
    let val run_attr = fold (curry (swap #> AU.apply_attribute attr #> fst))
    in Scan.depend (fn context => Scan.succeed (run_attr thms context, ())) end
in
val parse_add_context_update = parse_thms parse_add_arg_entry --
  (parse_opt_sep :|-- (fn opt_sep =>
      let val repeat = if is_none opt_sep then Scan.repeat else Scan.repeat1
      in Scan.lift (PU.position (gen_parse_add_arg_entries repeat) >> add_attribute) end))
  :|-- parse_run_attr
val parse_del_context_update = parse_thms parse_del_arg_entry
  -- (parse_opt_sep :|-- (fn opt_sep =>
      let val repeat = case opt_sep of NONE => Scan.repeat | SOME _ => Scan.repeat1
      in
        Scan.lift (PU.position (parse_del_arg_entries repeat)
        >> (apfst PDA.get_select_safe #> del_attribute))
      end))
  :|-- parse_run_attr
val parse_config_context_update = Scan.succeed []
  -- Scan.lift (PU.position parse_config_arg_entries >> config_attribute)
  :|-- parse_run_attr
end

(* action data *)
fun gen_focused_data focused_goals lookup x focus = focused_goals focus x
  |> maps (apsnd lookup #> (fn (i, datas) => List.map (snd #> pair (GFocus.single i)) datas))
fun focused_data_none_each x = gen_focused_data GFocus.focused_data_none_each x
fun focused_data_none_no x = gen_focused_data GFocus.focused_data_none_no x

fun tac_data_from_data meta tac data = {
  meta = meta,
  empty_action = PD.get_empty_action data,
  result_action = Result_Action.hom_changed_goals_action (PD.get_updates data) (PD.get_mk_cud data),
  prio_sq_co = PD.get_prio_sq_co data,
  tac = tac (PD.get_progress data) (PD.get_thm data)}

fun paction_data_from_data exn meta tac = tac_data_from_data meta tac
  #> Tac.paction_data_from_data exn

fun cons_action exn meta tac = paction_data_from_data exn meta tac #> Z.PAction.cons_action

local open MU.SC
in
fun cons_action_cluster exn meta tac ctxt =
  map_index (Library.uncurry (fn i => apsnd (fn data => fn focus =>
    let val meta = AMeta.metadata (
      Zippy_Identifier.suffix_name NONE (string_of_int i) (ACMeta.Id.getter meta),
      Lazy.lazy (fn _ => Pretty.breaks [
          Pretty.str (ACMeta.Descr.getter meta |> Lazy.force),
          Pretty.block [Pretty.str "Theorem: ", Thm.pretty_thm ctxt (PD.get_thm data)]
        ] |> Pretty.block |> Pretty.string_of))
    in cons_action exn meta tac data focus >>> Up4.morph end)))
  #> Node.cons3 exn meta
end
end
end
end