(*  Title:      Zippy/generic_term_index_data.ML
    Author:     Kevin Kappelmann

Term index stored in the generic context.
*)
@{parse_entries (sig) PARSE_GENERIC_TERM_INDEX_DATA_ARGS [add, del]}
signature GENERIC_TERM_INDEX_DATA =
sig
  include HAS_LOGGER
  structure PA : PARSE_GENERIC_TERM_INDEX_DATA_ARGS
  structure TI : TERM_INDEX

  type value
  val eq_value : value * value -> bool
  val pretty_value : Proof.context -> value -> Pretty.T

  type term_value = term * value
  val pretty_term_value : Proof.context -> term_value -> Pretty.T

  type index = term_value TI.term_index
  val pretty_index : Proof.context -> index -> Pretty.T

  structure Data : GENERIC_DATA
  where type T = index
  val get_index : Context.generic -> index
  val map_index : (index -> index) -> Context.generic -> Context.generic
  val pretty_Data : Proof.context -> Pretty.T

  val insert : term * value -> Context.generic -> Context.generic
  val delete : term * (term_value -> bool) -> Context.generic -> Context.generic

  val binding : Binding.binding
  val arg_parsers : ((string * ML_Code_Util.code, ML_Code_Util.code) Either.either parser,
    (string * ML_Code_Util.code, ML_Code_Util.code) Either.either parser) PA.entries
  val attribute : ((string * ML_Code_Util.code, ML_Code_Util.code) Either.either,
    (string * ML_Code_Util.code, ML_Code_Util.code) Either.either) PA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Generic_Term_Index_Data(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val parent_logger : Logger.logger_binding
    structure TI : TERM_INDEX
    type value
    val eq_value : value * value -> bool
    val pretty_value : Proof.context -> value -> Pretty.T
  end) : GENERIC_TERM_INDEX_DATA =
struct

open A
structure FI = Functor_Instance(A.FI)
structure Show = SpecCheck_Show_Base

val logger = Logger.setup_new_logger parent_logger FI.name

@{parse_entries (struct) PA [add, del]}

type term_value = term * value
fun pretty_term_value ctxt = Show.zip (Syntax.pretty_term ctxt) (pretty_value ctxt)

type index = term_value TI.term_index
fun pretty_index ctxt = TI.content #> Show.list (pretty_term_value ctxt)

val eq_insert = eq_snd eq_value
structure Data = Generic_Data(Term_Index_Generic_Data_Args(
  structure TI = TI
  type data = term_value
  val data_eq = eq_insert))

val get_index = Data.get
val map_index = Data.map
fun pretty_Data ctxt = get_index (Context.Proof ctxt) |> pretty_index ctxt

fun insert (t, value) context = map_index (fn ti =>
  let
    val ctxt = Context.proof_of context
    val term_value = (t, value)
    val key = TI.norm_term t
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.breaks [
        Pretty.block [Pretty.str "Inserting value ", pretty_value ctxt value],
        Pretty.block [Pretty.str "at key ", Syntax.pretty_term ctxt key, Pretty.str "."]
      ] |> Pretty.block |> Pretty.string_of);
    TI.insert (curry eq_insert term_value) (key, term_value) ti)
    handle Term_Index_Base.INSERT =>
      (@{log Logger.WARN} ctxt (fn _ =>
          Pretty.breaks [
          Pretty.block [Pretty.str "Value ", pretty_value ctxt value],
          Pretty.block [Pretty.str "already added at key ", Syntax.pretty_term ctxt key, Pretty.str "."]
        ] |> Pretty.block |> Pretty.string_of);
      ti)
  end) context

fun delete (t, select) context = map_index (fn ti =>
  let
    val ctxt = Context.proof_of context
    val key = TI.norm_term t
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Deleting from key ", Syntax.pretty_term ctxt key
      ] |> Pretty.string_of);
    TI.delete select key ti)
    handle Term_Index_Base.DELETE =>
      (@{log Logger.WARN} (Context.proof_of context) (fn _ => Pretty.block [
        Pretty.str "No matching data for key ", Syntax.pretty_term ctxt key, Pretty.str " found."
      ] |> Pretty.string_of);
      ti)
  end) context

val binding = Binding.make (FI.id, FI.pos)

val arg_parsers = {
  add = SOME (
    Parse_Util.parenths (Parse.term --| Parse.$$$ "," --
      Parse_Util.nonempty_code (K "value to add must not be empty"))
    >> Either.Left
    || Parse_Util.nonempty_code (K "data to add must not be empty") >> Either.Right),
  del = SOME (
    Parse_Util.parenths (Parse.term --| Parse.$$$ "," --
      Parse_Util.nonempty_code (K "selector for deletion must not be empty"))
    >> Either.Left
    || Parse_Util.nonempty_code (K "data for deletion must not be empty") >> Either.Right)
}

val parse_arg_entries =
  let
    val parse_value = PA.parse_entry (PA.get_add arg_parsers) (PA.get_del arg_parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key Parse_Util.eq parse_value
  in PA.parse_entries_required Parse.and_list1 [] parse_entry (PA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun default (context, _) = (SOME context, NONE)
    val run_code = ML_Attribute.run_map_context o rpair pos
    fun prepare_term context =
      let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of context)
      in Syntax.read_term ctxt #> ML_Syntax.print_term #> ML_Code_Util.read end
    val add = case PA.get_add_safe entries of
        SOME res => (fn x as (context, _) =>
          let val c = Either.cases (fn (t, c) => ML_Code_Util.tuple [prepare_term context t, c]) I res
          in run_code (FI.code_struct_op "insert" @ c) x end)
      | NONE => default
    val del = case PA.get_del_safe entries of
        SOME res => (fn x as (context, _) =>
          let val c = Either.cases (fn (t, c) => ML_Code_Util.tuple [prepare_term context t, c]) I res
          in run_code (FI.code_struct_op "delete" @ c) x end)
      | NONE => default
  in ML_Attribute_Util.apply_attribute del #> add end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("add/del term index data " ^ enclose "(" ")" FI.long_name)
end
