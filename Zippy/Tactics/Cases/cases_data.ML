(*  Title:      Zippy/cases_data.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_CASES_DATA_MODE [add, del, config]}
@{parse_entries (sig) PARSE_CASES_DATA [insts, rule, simp, facts, match]}
@{parse_entries (sig) PARSE_CASES_DATA_OPT [rule, simp, facts, match]}
@{parse_entries (sig) PARSE_CASES_DATA_ADD_DEL_ARGS [insts, simp, facts, match]}
@{parse_entries (sig) PARSE_CASES_DATA_OPT_ADD_DEL_ARGS [simp, facts, match]}
@{parse_entries (sig) PARSE_CASES_DATA_CONFIG [simp, match]}
@{parse_entries (sig) PARSE_CASES_DATA_INSTS_MODES [pred, pat, fix]}

signature CASES_DATA_ARGS =
sig
  structure PM : PARSE_CASES_DATA_MODE
  structure PD : PARSE_CASES_DATA
  structure POD : PARSE_CASES_DATA_OPT
  structure PADA : PARSE_CASES_DATA_ADD_DEL_ARGS
  structure POADA : PARSE_CASES_DATA_OPT_ADD_DEL_ARGS
  structure PDC : PARSE_CASES_DATA_CONFIG
  structure PIM : PARSE_CASES_DATA_INSTS_MODES

  val PD_entries_from_POD_entries : ('a, 'b, 'c, 'd) POD.entries -> 'e ->
    ('e, 'a, 'b, 'c, 'd) PD.entries
  val POD_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e) PD.entries -> ('b, 'c, 'd, 'e) POD.entries
  val POADA_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e) PD.entries -> ('c, 'd, 'e) POADA.entries
  val PADA_entries_from_POADA_entries : ('a, 'b, 'c) POADA.entries -> 'd ->
    ('d, 'a, 'b, 'c) PADA.entries
  val PADA_entries_from_PD_entries : ('a, 'b, 'c, 'd, 'e) PD.entries -> ('a, 'c, 'd, 'e) PADA.entries
  val PD_entries_from_PADA_entries : ('a, 'b, 'c, 'd) PADA.entries -> 'e ->
    ('a, 'e, 'b, 'c, 'd) PD.entries

  type insts = ((term -> bool) option list, (term * term list) option list, term option list)
    PIM.entry
  val insts_ord : insts ord
  val pretty_insts : Proof.context -> insts -> Pretty.T

  type match = term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool
  type data = (insts, thm option, bool, thm list, match) PD.entries
  type add_del_args = (insts, bool, thm list, match) PADA.entries
  val data_ord : data ord
  val eq_data : data * data -> bool
  val pretty_data : Proof.context -> data -> Pretty.T
  val transfer_data : theory -> data -> data

  type config_data = (bool, match) PDC.entries

  val data_parsers : (unit context_parser ->
      (ML_Code_Util.code option list, (term * term list) option list, term option list) PIM.entry
        context_parser,
    thm context_parser, bool parser, thm list context_parser, ML_Code_Util.code parser) PD.entries
  val config_data_parsers : (bool parser, ML_Code_Util.code parser) PDC.entries
end

structure Cases_Data_Args : CASES_DATA_ARGS =
struct

structure PU = Parse_Util
structure Show = SpecCheck_Show

@{parse_entries (struct) PM [add, del, config]}
@{parse_entries (struct) PD [insts, rule, simp, facts, match]}
@{parse_entries (struct) POD [rule, simp, facts, match]}
@{parse_entries (struct) PADA [insts, simp, facts, match]}
@{parse_entries (struct) POADA [simp, facts, match]}
@{parse_entries (struct) PDC [simp, match]}
@{parse_entries (struct) PIM [pred, pat, fix]}

fun PD_entries_from_POD_entries {rule, simp, facts, match} insts =
  {insts = SOME insts, rule = rule, simp = simp, facts = facts, match = match}
fun POD_entries_from_PD_entries {rule, simp, facts, match,...} =
  {rule = rule, simp = simp, facts = facts, match = match}
fun POADA_entries_from_PD_entries {simp, facts, match,...} =
  {simp = simp, facts = facts, match = match}
fun PADA_entries_from_POADA_entries {simp, facts, match} insts =
  {insts = SOME insts, simp = simp, facts = facts, match = match}
fun PADA_entries_from_PD_entries {insts, simp, facts, match,...} =
  {insts = insts, simp = simp, facts = facts, match = match}
fun PD_entries_from_PADA_entries {insts, simp, facts, match} rule =
  {insts = insts, rule = SOME rule, simp = simp, facts = facts, match = match}

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
type data = (insts, thm option, bool, thm list, match) PD.entries
type add_del_args = (insts, bool, thm list, match) PADA.entries

val data_ord = option_ord Thm.thm_ord o apply2 PD.get_rule
  ||| insts_ord o apply2 PD.get_insts
  ||| list_ord Thm.thm_ord o apply2 PD.get_facts
  ||| bool_ord o apply2 PD.get_simp
val eq_data = is_equal o data_ord
fun pretty_data ctxt data = Show.record [
  ("rule", Show.option (Show.thm ctxt) (PD.get_rule data)),
  ("insts", pretty_insts ctxt (PD.get_insts data)),
  ("facts", Show.list (Show.thm ctxt) (PD.get_facts data)),
  ("simp", Show.bool (PD.get_simp data))
]
fun transfer_data thy = PD.map_rule (Option.map (Thm.transfer thy))
  #> PD.map_facts (map (Thm.transfer thy))

type config_data = (bool, match) PDC.entries

val parse_insts_pred = ML_Code_Util.parse_code
fun maybe' scan = Scan.lift Parse.underscore >> K NONE || scan >> SOME
val parse_insts_pattern = maybe' (PU.term_pattern >> rpair []
  || PU.parens' (Parse.!!!!
    (PU.term_pattern --| Scan.lift (Parse.$$$ ",") -- Scan.repeat1 PU.term_pattern)))
val parse_insts_fix = maybe' PU.term
fun parse_insts unless =
  Scan.lift (Scan.option (Args.parens PIM.parse_key))
  :|-- (fn opt_key =>
    let fun repeat_unless parse = (if is_none opt_key then Scan.repeat else Scan.repeat1)
      (Scan.unless unless parse)
    in case the_default (PIM.key PIM.fix) opt_key of
      PIM.pred _ => repeat_unless (Scan.lift (Parse.maybe parse_insts_pred)) >> PIM.pred
    | PIM.pat _ => repeat_unless parse_insts_pattern >> PIM.pat
    | PIM.fix _ => repeat_unless parse_insts_fix >> PIM.fix
    end)

val data_parsers = {
  insts = SOME parse_insts,
  rule = SOME PU.thm,
  simp = SOME PU.bool,
  facts = SOME (PU.nonempty_thms (K "must provide at least one fact")),
  match = SOME (PU.nonempty_code (K "match selector must not be empty"))
}
val config_data_parsers = {
  simp = PD.get_simp_safe data_parsers,
  match = PD.get_match_safe data_parsers
}
end

signature CASES_DATA =
sig
  include HAS_LOGGER

  structure Config_Data : GENERIC_DATA
  where type T = Cases_Data_Args.config_data

  val get_config_data : Context.generic -> Config_Data.T
  val map_config_data : (Config_Data.T -> Config_Data.T) -> Context.generic -> Context.generic

  val get_simp : Context.generic -> bool
  val map_simp : (bool -> bool) -> Context.generic -> Context.generic

  val get_match : Context.generic -> Cases_Data_Args.match
  val map_match : (Cases_Data_Args.match -> Cases_Data_Args.match) ->
    Context.generic -> Context.generic

  structure Data : GENERIC_DATA
  where type T = Cases_Data_Args.data list

  val insert : Cases_Data_Args.data -> Context.generic -> Context.generic
  val insert_add_args : Cases_Data_Args.add_del_args -> thm -> Context.generic -> Context.generic
  val insert_add_args_context_defaults : Cases_Data_Args.add_del_args -> thm ->
    Context.generic -> Context.generic

  val delete : Cases_Data_Args.data -> Context.generic -> Context.generic
  val delete_del_args : Cases_Data_Args.add_del_args -> thm -> Context.generic -> Context.generic
  val delete_del_args_context_defaults : Cases_Data_Args.add_del_args -> thm ->
    Context.generic -> Context.generic

  val cases_tac :
    (bool -> thm option -> term option list -> thm list -> Proof.context -> int -> tactic) ->
    Cases_Data_Args.data -> Proof.context -> int -> tactic

  val binding : Binding.binding
  val parse_add_del_arg_entries : ((ML_Code_Util.code option list,
      (term * term list) option list, term option list) Cases_Data_Args.PIM.entry,
    bool, thm list, ML_Code_Util.code) Cases_Data_Args.PADA.entries context_parser

  structure Facts_Data_Internal : GENERIC_DATA

  val add_attribute : ((ML_Code_Util.code option list, (term * term list) option list,
      term option list) Cases_Data_Args.PIM.entry,
    bool, thm list, ML_Code_Util.code) Cases_Data_Args.PADA.entries * Position.T -> attribute
  val del_attribute : ((ML_Code_Util.code option list, (term * term list) option list,
      term option list) Cases_Data_Args.PIM.entry,
    bool, thm list, ML_Code_Util.code) Cases_Data_Args.PADA.entries * Position.T -> attribute

  val parse_config_arg_entries : (bool, ML_Code_Util.code) Cases_Data_Args.PDC.entries parser
  val config_attribute : ((bool, ML_Code_Util.code) Cases_Data_Args.PDC.entries * Position.T) ->
    attribute

  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_arg_entries : ((ML_Code_Util.code option list,
      (term * term list) option list, term option list) Cases_Data_Args.PIM.entry,
    thm, bool, thm list, ML_Code_Util.code) Cases_Data_Args.PD.entries context_parser
  val parse_add_context_update : unit context_parser
  val parse_del_context_update : unit context_parser
  val parse_config_context_update : unit context_parser
  val parse_entry_context_update : unit context_parser
  val parse_context_update : unit context_parser
end

functor Cases_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Cases : CASES_TACTIC
    val init_config_data : Cases_Data_Args.config_data
    val parent_logger : Logger.logger_binding
  ) : CASES_DATA =
struct

val logger = Logger.setup_new_logger parent_logger "Cases_Data"
structure FI = Functor_Instance(FI)

structure CTA = Cases_Data_Args
structure PD = CTA.PD
structure POD = CTA.POD
structure PADA = CTA.PADA
structure POADA = CTA.POADA
structure PDC = CTA.PDC
structure PM = CTA.PM
structure PIM = CTA.PIM

structure AU = ML_Attribute_Util
structure MCU = ML_Code_Util
structure PU = Parse_Util

structure Config_Data = Generic_Data(
  type T = CTA.config_data
  val empty = init_config_data
  val merge = fst)

val get_config_data = Config_Data.get
val map_config_data = Config_Data.map

val get_simp = PDC.get_simp o get_config_data
val map_simp = map_config_data o PDC.map_simp

val get_match = PDC.get_match o get_config_data
val map_match = map_config_data o PDC.map_match

structure Data = Generic_Data(
  type T = CTA.data list
  val empty = []
  val merge = Ord_List.merge CTA.data_ord)

fun insert args context = context |>
  let val args = PD.map_rule (Option.map Thm.trim_context) args
    |> PD.map_facts (map Thm.trim_context)
  in
    Data.map (fn data => if Ord_List.member CTA.data_ord data args
      then let val ctxt = (Context.proof_of context)
        in
          (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
              Pretty.str "Similar cases data already added. Skipping insertion of",
              CTA.pretty_data ctxt args
            ] |> Pretty.block |> Pretty.string_of);
          data)
        end
      else Ord_List.insert CTA.data_ord args data)
  end

fun prepare_attr_rule thm = if Thm.is_dummy thm then NONE else SOME thm

fun insert_add_args args thm = insert
  (CTA.PD_entries_from_PADA_entries args (prepare_attr_rule thm))

fun add_del_args_context_defaults args context =
  let val default_entries = get_config_data context
    |> (fn cargs => [PADA.simp (PDC.get_simp cargs), PADA.match (PDC.get_match cargs)])
    |> PADA.entries_from_entry_list
  in PADA.merge_entries args default_entries end

fun insert_add_args_context_defaults args thm context =
  insert_add_args (add_del_args_context_defaults args context) thm context

fun delete args context = Data.map (fn data => if Ord_List.member CTA.data_ord data args
  then Ord_List.remove CTA.data_ord args data
  else let val ctxt = (Context.proof_of context)
    in
      (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
          Pretty.str "Cases data", CTA.pretty_data ctxt args, Pretty.str "not found. Skipping deletion."
        ] |> Pretty.block |> Pretty.string_of);
      data)
    end) context
fun delete_del_args args thm = delete
  (CTA.PD_entries_from_PADA_entries args (prepare_attr_rule thm))
fun delete_del_args_context_defaults args thm context =
  delete_del_args (add_del_args_context_defaults args context) thm context

fun cases_tac cases_fixed_tac args =
  let fun app_args tac insts = tac (PD.get_simp args) (PD.get_rule args) insts (PD.get_facts args)
  in case PD.get_insts args of
    PIM.pred p => app_args Cases.cases_find_insts_tac p
  | PIM.pat p => app_args (fn x => Cases.cases_pattern_tac x (PD.get_match args)) p
  | PIM.fix p => app_args cases_fixed_tac p
  end

val binding = Binding.make (FI.prefix_id "cases", FI.pos)

fun gen_filter_arg_entries get_insts get_match_safe =
  let
    fun filter entries = case (get_insts entries, get_match_safe entries) of
      (PIM.pat _, SOME _) => false | _ => true
    val filter_msg = "Match must only be passed when using patterns for instantiations"
  in PU.filter filter (K (PU.fail (K filter_msg))) end

val parse_insts_opt_args_sep = Scan.lift (Args.$$$ "use")

fun gen_parse_arg_entries parse_entries_required parse_entry get_insts get_match_safe
  entries_from_opt_entries default_entries =
  let val unless = (parse_insts_opt_args_sep >> K ()) || (parse_entry >> K ())
  in
    Scan.optional (PD.get_insts CTA.data_parsers unless) (PIM.fix [])
    -- (Scan.option parse_insts_opt_args_sep
    :|-- (fn use => parse_entries_required (if is_some use then Scan.repeat1 else Scan.repeat)
      true [] parse_entry default_entries))
    >> (fn (insts, entries) => entries_from_opt_entries entries insts)
    |> gen_filter_arg_entries get_insts get_match_safe
  end

val parse_add_del_arg_entries =
  let
    val parsers = CTA.POADA_entries_from_PD_entries CTA.data_parsers
    val parse_value = POADA.parse_entry (Scan.lift (POADA.get_simp parsers))
      (POADA.get_facts parsers) (Scan.lift (POADA.get_match parsers))
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift POADA.parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value
    val default_entries = [POADA.facts []] |> POADA.entries_from_entry_list
  in
    gen_parse_arg_entries POADA.parse_entries_required' parse_entry PADA.get_insts
      PADA.get_match_safe CTA.PADA_entries_from_POADA_entries default_entries
  end

fun Args_substructure_op substructure operation =
  MCU.flat_read ["Cases_Data_Args.", substructure, ".", operation]

structure Facts_Data_Internal = Generic_Data(
  type T = thm list
  val empty = []
  val merge = fst)

fun code_bool b = MCU.read (if b then "true" else "false")

fun gen_attribute operation (entries, pos) (context, thm) =
  let
    val code_PADA_op = Args_substructure_op "PADA"
    val code_PIM_op = Args_substructure_op "PIM"
    val code_from_key = code_PADA_op o PADA.key_to_string
    val code_term = ML_Syntax.print_term #> MCU.read
    val context = Facts_Data_Internal.put (PADA.get_facts entries) context
    fun code_from_entry (PADA.simp b) = code_bool b
      | code_from_entry (PADA.insts (PIM.pred insts)) = code_PIM_op "pred" @
          (insts |> List.map (Option.map MCU.atomic #> MCU.option) |> MCU.list)
      | code_from_entry (PADA.insts (PIM.pat insts)) = code_PIM_op "pat" @ (insts
          |> map (Option.map (fn (t, ts) => MCU.tuple [code_term t, map code_term ts |> MCU.list])
            #> MCU.option)
          |> MCU.list)
      | code_from_entry (PADA.insts (PIM.fix insts)) = code_PIM_op "fix" @
          (insts |> List.map (Option.map (code_term #> MCU.atomic) #> MCU.option) |> MCU.list)
      | code_from_entry (PADA.facts _) = FI.code_struct_op "Facts_Data_Internal.get"
      | code_from_entry (PADA.match c) = c
    val code_entries = PADA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      let val [thm, context, get_facts] = map MCU.internal_name ["thm", "context", "get_facts"]
      in
        MCU.reads ["fn", thm, "=> fn", context, "=>"] @ FI.code_struct_op operation @
          MCU.atomic (code_PADA_op "entries_from_entry_list" @ code_entries @
            MCU.read "|>" @ code_PADA_op "map_facts" @
              MCU.atomic (MCU.reads ["fn", get_facts, "=>", get_facts, context])) @
          MCU.reads [thm, context]
      end
  in ML_Attribute.run_declaration_attribute (code, pos) (context, thm) end

val add_attribute = gen_attribute "insert_add_args_context_defaults"
val del_attribute = gen_attribute "delete_del_args_context_defaults"

val parse_config_arg_entries =
  let
    val parsers = CTA.config_data_parsers
    val parse_value = PDC.parse_entry (PDC.get_simp parsers) (PDC.get_match parsers)
    val parse_entry = Parse_Key_Value.parse_entry PDC.parse_key (K (Parse.$$$ ":")) parse_value
    val default_entries = PDC.empty_entries ()
  in PDC.parse_entries_required Scan.repeat1 true [] parse_entry default_entries end

fun config_attribute (entries, pos) =
  let
    val code_PDC_op = Args_substructure_op "PDC"
    val code_from_key = code_PDC_op o PDC.key_to_string
    fun code_from_entry (PDC.simp b) = code_bool b
      | code_from_entry (PDC.match c) = c
    val code_entries = PDC.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FI.code_struct_op "map_config_data" @ MCU.atomic (code_PDC_op "merge_entries" @
      MCU.atomic (code_PDC_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_entries =
  let
    val parse_value = PM.parse_entry parse_add_del_arg_entries parse_add_del_arg_entries
      (Scan.lift parse_config_arg_entries)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PM.parse_key) (K (Scan.succeed ""))
      parse_value
  in PM.parse_entries_required' Parse.and_list1' true [] parse_entry (PM.empty_entries ()) end

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

val parse_attribute = PU.position' parse_entries >> attribute
  || PU.position' parse_add_del_arg_entries >> add_attribute

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("configure cases data " ^ enclose "(" ")" FI.long_name)

val parse_arg_entries =
  let
    val parsers = CTA.POD_entries_from_PD_entries CTA.data_parsers
    val parse_value = POD.parse_entry (POD.get_rule parsers) (Scan.lift (POD.get_simp parsers))
      (POD.get_facts parsers) (Scan.lift (POD.get_match parsers))
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift POD.parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value
    val default_entries = [POD.facts []] |> POD.entries_from_entry_list
  in
    gen_parse_arg_entries POD.parse_entries_required' parse_entry PD.get_insts
      PD.get_match_safe CTA.PD_entries_from_POD_entries default_entries
  end

local
  fun run_attr attr (context, opt_thm) = (case opt_thm of
      NONE => AU.attribute_map_context attr context
    | SOME thm => AU.apply_attribute attr (context, thm) |> fst)
    |> rpair () |> Scan.succeed
  fun gen_add_del_attr_context_update attr = PU.position' parse_arg_entries
    :|-- (fn (entries, pos) => Scan.depend (fn context => run_attr
      (attr (CTA.PADA_entries_from_PD_entries entries, pos)) (context, PD.get_rule_safe entries)))
in
val parse_add_context_update = gen_add_del_attr_context_update add_attribute
val parse_del_context_update = gen_add_del_attr_context_update del_attribute
val parse_config_context_update = Scan.lift (PU.position parse_config_arg_entries)
  :|-- (fn parsed => Scan.depend (fn context => run_attr (config_attribute parsed) (context, NONE)))
end

val parse_entry_context_update =
  Scan.optional (Scan.lift PM.parse_key) (PM.key PM.add)
  :|-- (fn PM.add _ => parse_add_context_update | PM.del _ => parse_del_context_update
    | PM.config _ => parse_config_context_update)
val parse_context_update = Parse.and_list1' parse_entry_context_update >> K ()

end