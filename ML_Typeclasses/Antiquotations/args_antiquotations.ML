(*  Title:      ML_Typeclasses/args_antiquotations.ML
    Author:     Kevin Kappelmann

Antiquotation for lists of arguments.
*)
@{parse_entries (sig) PARSE_ARGS_ANTIQUOTATIONS_ARGS [args, sep, encl, encl_arg, start, stop]}
@{parse_entries (sig) PARSE_ARGS_ANTIQUOTATIONS_ARG_ARGS [args, encl, n]}
@{parse_entries (sig) PARSE_ARGS_ANTIQUOTATIONS_ARG_CONTEXT_ARGS [args, encl]}

signature ARGS_ANTIQUOTATIONS_ARGS =
sig
  structure PAS : PARSE_ARGS_ANTIQUOTATIONS_ARGS
  structure PA : PARSE_ARGS_ANTIQUOTATIONS_ARG_ARGS
  structure PCA : PARSE_ARGS_ANTIQUOTATIONS_ARG_CONTEXT_ARGS
  val PCA_entries_from_PA_entries : ('a, 'b, 'c) PA.entries -> ('a, 'b) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b) PCA.entries -> 'c -> ('a, 'b, 'c) PA.entries

  type args_args = (string list, string, string * string, string * string, int, int option)
    PAS.entries
  type arg_args = (string list, string * string, int) PA.entries
  type arg_context_args = (string list, string * string) PCA.entries
  val nargs : args_args -> int
  val mk_args_code : args_args -> string
  val mk_arg_code : arg_args -> string
  val args_arg_parsers : (string list parser, string parser, (string * string) parser,
    (string * string) parser, int context_parser, int option context_parser) PAS.entries
  val arg_arg_parsers : (string list parser, (string * string) parser, int context_parser)
    PA.entries
end

structure Args_Antiquotations_Args : ARGS_ANTIQUOTATIONS_ARGS =
struct

structure PU = Parse_Util

@{parse_entries (struct) PAS [args, sep, encl, encl_arg, start, stop]}
@{parse_entries (struct) PA [args, encl, n]}
@{parse_entries (struct) PCA [args, encl]}
fun PCA_entries_from_PA_entries {args, encl,...} = {args = args, encl = encl}
fun PA_entries_from_PCA_entries {args, encl} n = {args = args, encl = encl, n = SOME n}

type args_args = (string list, string, string * string, string * string, int, int option)
  PAS.entries
type arg_args = (string list, string * string, int) PA.entries
type arg_context_args = (string list, string * string) PCA.entries

fun nargs entries = case (PAS.get_start entries, PAS.get_stop entries) of
    (start, NONE) => length (PAS.get_args entries) - start
  | (start, SOME stop) => stop + 1 - start

fun mk_args_code entries = PAS.get_args entries
  |> (case (PAS.get_start entries, PAS.get_stop entries) of
      (start, NONE) => drop start
    | (start, SOME stop) => drop start #> take (stop + 1 - start))
  |> map (uncurry enclose (PAS.get_encl_arg entries))
  |> space_implode (PAS.get_sep entries)
  |> uncurry enclose (PAS.get_encl entries)

fun mk_arg_code entries = PA.get_args entries
  |> (fn args => nth args (PA.get_n entries))
  |> uncurry enclose (PA.get_encl entries)

val args_parser = \<^keyword>\<open>[\<close> |-- Parse.list Parse.embedded --| \<^keyword>\<open>]\<close>
val encl_parser = Parse.embedded -- Parse.embedded
fun nonneg_n_parser fail_empty fail_neg = PU.filter (curry (op <=) 0)
  (PU.fail fail_neg) (PU.ML_int fail_empty)

val args_arg_parsers = {
  args = SOME args_parser,
  sep = SOME Parse.embedded,
  encl = SOME encl_parser,
  encl_arg = SOME encl_parser,
  start = SOME (nonneg_n_parser (K "start index must not be empty")
      (K "start index must be non-negative")),
  stop = SOME (nonneg_n_parser (K "stop index must not be empty")
      (K "stop index must be non-negative")
    |> PU.option')
}

val arg_arg_parsers = {
  args = SOME args_parser,
  encl = SOME encl_parser,
  n = SOME (nonneg_n_parser (K "argument number must not be empty")
    (K "argument number must be non-negative"))
}
end

signature ARGS_ANTIQUOTATIONS =
sig
  structure Data : GENERIC_DATA
  val get_data : Context.generic -> Data.T
  val map_data : (Data.T -> Data.T) -> Context.generic -> Context.generic

  val get_args : Context.generic -> string list
  val map_args : (string list -> string list) -> Context.generic -> Context.generic

  val get_sep : Context.generic -> string
  val map_sep : (string -> string) -> Context.generic -> Context.generic

  val get_encl : Context.generic -> string * string
  val map_encl : (string * string -> string * string) -> Context.generic -> Context.generic

  val get_encl_arg : Context.generic -> string * string
  val map_encl_arg : (string * string -> string * string) -> Context.generic -> Context.generic

  val get_start : Context.generic -> int
  val map_start : (int -> int) -> Context.generic -> Context.generic

  val get_stop : Context.generic -> int option
  val map_stop : (int option -> int option) -> Context.generic -> Context.generic

  val nargs : Context.generic -> int

  val mk_args_code : Proof.context -> string
  val mk_arg_code : int -> Proof.context -> string

  val args_binding : binding
  val arg_binding : binding

  val args_attribute : Args_Antiquotations_Args.args_args -> attribute
  val parse_args_attribute : attribute context_parser
  val setup_args_attribute : string option -> local_theory -> local_theory

  val parse_args_antiquotation : (Proof.context -> string) context_parser
  val setup_args_antiquotation : theory -> theory

  val parse_arg_antiquotation : (Proof.context -> string) context_parser
  val setup_arg_antiquotation : theory -> theory
end

functor Args_Antiquotations(
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : Args_Antiquotations_Args.args_args
  ) : ARGS_ANTIQUOTATIONS =
struct

structure AAA = Args_Antiquotations_Args
structure PAS = AAA.PAS
structure PA = AAA.PA
structure PCA = AAA.PCA
structure FIU = Functor_Instance_Util(FIA)

structure Data = Generic_Data(
  type T = AAA.args_args
  val empty = init_args
  val merge = fst
)

val get_data = Data.get
val map_data = Data.map

val get_args = PAS.get_args o get_data
val map_args = map_data o PAS.map_args

val get_sep = PAS.get_sep o get_data
val map_sep = map_data o PAS.map_sep

val get_encl = PAS.get_encl o get_data
val map_encl = map_data o PAS.map_encl

val get_encl_arg = PAS.get_encl_arg o get_data
val map_encl_arg = map_data o PAS.map_encl_arg

val get_start = PAS.get_start o get_data
val map_start = map_data o PAS.map_start

val get_stop = PAS.get_stop o get_data
val map_stop = map_data o PAS.map_stop

fun nargs context = AAA.nargs (get_data context)
fun mk_args_code ctxt = AAA.mk_args_code (get_data (Context.Proof ctxt))

fun PCA_entries_from_PAS_entries {args, encl_arg,...} = {args = args, encl = encl_arg}
fun PAS_entries_from_PCA_entries entries = PAS.empty_entries ()
  |> PAS.map_args_safe (PCA.get_args_safe entries |> K)
  |> PAS.map_encl_arg_safe (PCA.get_encl_safe entries |> K)

fun mk_arg_code n ctxt =
  AAA.PA_entries_from_PCA_entries (PCA_entries_from_PAS_entries (get_data (Context.Proof ctxt))) n
  |> AAA.mk_arg_code

val args_binding = FIU.mk_binding_id_prefix "args"
val arg_binding = FIU.mk_binding_id_prefix "arg"

val parse_args_entries =
  let
    val parsers = AAA.args_arg_parsers
    val parse_value = PAS.parse_entry (PAS.get_args parsers |> Scan.lift)
      (PAS.get_sep parsers |> Scan.lift) (PAS.get_encl parsers |> Scan.lift)
      (PAS.get_encl_arg parsers |> Scan.lift) (PAS.get_start parsers) (PAS.get_stop parsers)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PAS.parse_key)
      (Scan.lift Parse_Util.eq) parse_value
    val required_keys = []
    val default_entries = PAS.empty_entries ()
  in PAS.parse_entries_required' Parse.and_list1' required_keys parse_entry default_entries end

fun args_attribute entries = Thm.declaration_attribute (K (map_data (PAS.merge_entries entries)))

val parse_args_attribute = parse_args_entries >> args_attribute

val setup_args_attribute = Attrib.local_setup args_binding (Parse.!!!! parse_args_attribute) o
  the_default ("set args antiquotation arguments (" ^ FIU.FIA.full_name ^ ")")

val parse_args_antiquotation =
  (parse_args_attribute |> Parse_Util.option')
  >> (fn opt_attr =>
    the_default I (Option.map ML_Attribute_Util.attribute_map_ctxt opt_attr)
    #> mk_args_code)

val setup_args_antiquotation = ML_Antiquotation.declaration args_binding parse_args_antiquotation
  (K (fn mk_code => pair (mk_code #> pair "")))

val parse_arg_entries =
  let
    val parsers = AAA.arg_arg_parsers |> AAA.PCA_entries_from_PA_entries
    val parse_value = PCA.parse_entry (PCA.get_args parsers |> Scan.lift)
      (PCA.get_encl parsers |> Scan.lift)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PCA.parse_key)
      (Scan.lift Parse_Util.eq) parse_value
    val required_keys = []
    val default_entries = PCA.empty_entries ()
  in PCA.parse_entries_required' Parse.and_list1' required_keys parse_entry default_entries end

fun arg_attribute entries=
  Thm.declaration_attribute (K (map_data (PAS.merge_entries (PAS_entries_from_PCA_entries entries))))

val parse_arg_attribute = parse_arg_entries >> arg_attribute

val parse_arg_antiquotation =
  PA.get_n AAA.arg_arg_parsers
  -- ((Scan.lift Parse.where_ |-- parse_arg_attribute) |> Parse.!!!! |> Parse_Util.option')
  >> (fn (n, opt_attr) =>
    the_default I (Option.map ML_Attribute_Util.attribute_map_ctxt opt_attr)
    #> mk_arg_code n)

val setup_arg_antiquotation = ML_Antiquotation.declaration arg_binding parse_arg_antiquotation
  (K (fn mk_code => pair (mk_code #> pair "")))

end