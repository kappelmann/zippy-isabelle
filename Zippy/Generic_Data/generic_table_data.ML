(*  Title:      Zippy/generic_table_data.ML
    Author:     Kevin Kappelmann

Table stored in the generic context.
*)
@{parse_entries (sig) PARSE_GENERIC_TABLE_DATA_ARGS [add, del]}

signature GENERIC_TABLE_DATA =
sig
  include HAS_LOGGER
  structure PA : PARSE_GENERIC_TABLE_DATA_ARGS

  type key
  structure Table : TABLE
  sharing type Table.key = key
  val pretty_key : key -> Pretty.T

  type value

  type table = value Table.table
  val pretty_table : Proof.context -> table -> Pretty.T

  structure Data : GENERIC_DATA
  where type T = table
  val get_table : Context.generic -> table
  val map_table : (table -> table) -> Context.generic -> Context.generic
  val pretty_Data : Proof.context -> Pretty.T

  val insert : key * value -> Context.generic -> Context.generic
  val delete : key -> Context.generic -> Context.generic

  val binding : Binding.binding
  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser) PA.entries
  val attribute : (ML_Code_Util.code, ML_Code_Util.code) PA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Generic_Table_Data(A : sig
  structure FI : FUNCTOR_INSTANCE_BASE
  val parent_logger : Logger.logger_binding
  type key
  val ord_key : key ord
  val pretty_key : key -> Pretty.T
  type value
  val pretty_value : Proof.context ->value -> Pretty.T
  end) : GENERIC_TABLE_DATA =
struct

open A
structure FI = Functor_Instance(A.FI)
structure Show = SpecCheck_Show_Base

val logger = Logger.setup_new_logger parent_logger FI.name

@{parse_entries (struct) PA [add, del]}

structure Table = Table(type key = key; val ord = ord_key)
fun pretty_key_value ctxt = Show.zip pretty_key (pretty_value ctxt)
fun pretty_table ctxt = Table.dest #> Show.list (pretty_key_value ctxt)

type table = value Table.table

structure Data = Generic_Data(
  type T = table
  val empty = Table.empty
  val merge = Table.merge (K true))

val get_table = Data.get
val map_table = Data.map
fun pretty_Data ctxt = Context.Proof ctxt |> get_table |> pretty_table ctxt

fun insert (key, value) context = map_table (fn table =>
  let val ctxt = Context.proof_of context
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "Inserting with key ", pretty_key key, Pretty.str "."
    ] |> Pretty.string_of);
    Table.insert (K false) (key, value) table)
    handle Table.DUP _ =>
      (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
        Pretty.str "Key ", pretty_key key, Pretty.str " already added."
      ] |> Pretty.string_of);
      table)
  end) context

fun delete key context = map_table (fn table =>
  let val ctxt = Context.proof_of context
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "Deleting key ", pretty_key key, Pretty.str "."
    ] |> Pretty.string_of);
    Table.delete key table)
    handle Table.UNDEF _ =>
      (@{log Logger.WARN} (Context.proof_of context) (fn _ => Pretty.block [
        Pretty.str "Key ", pretty_key key, Pretty.str " not found."
      ] |> Pretty.string_of);
      table)
  end) context

val binding = Binding.make (FI.id, FI.pos)

val arg_parsers = {
  add = SOME (Parse_Util.nonempty_code (K "data to add must not be empty")),
  del = SOME (Parse_Util.nonempty_code (K "key to delete must not be empty"))
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
    val add = case PA.get_add_safe entries of
        SOME c => FI.code_struct_op "insert" @ ML_Code_Util.atomic c |> run_code
      | NONE => default
    val del = case PA.get_del_safe entries of
        SOME c => FI.code_struct_op "delete" @ ML_Code_Util.atomic c |> run_code
      | NONE => default
  in ML_Attribute_Util.apply_attribute del #> add end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("add/del table data " ^ enclose "(" ")" FI.long_name)
end
