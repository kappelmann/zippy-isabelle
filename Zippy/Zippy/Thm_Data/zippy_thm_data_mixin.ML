(*  Title:      Zippy/zippy_thm_data_mixin.ML
    Author:     Kevin Kappelmann
*)
@{parse_entries (sig) PARSE_ZIPPY_THM_DATA_MIXIN_ARGS [add, del]}
signature ZIPPY_THM_DATA_MIXIN =
sig
  include ZIPPY_THM_DATA_MIXIN_BASE
  structure PA : PARSE_ZIPPY_THM_DATA_MIXIN_ARGS

  val key_of_thm : thm -> term

  val term_value_thm : Data.term_value -> thm
  val term_value_data : Data.term_value -> data

  val insert : thm -> data -> Context.generic -> Context.generic
  val delete : thm -> (Data.term_value -> bool) -> Context.generic -> Context.generic

  val binding : Binding.binding
  val arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser) PA.entries
  val attribute : (ML_Code_Util.code, ML_Code_Util.code) PA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory
end

functor Zippy_Thm_Data_Mixin(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Thm_Data : ZIPPY_THM_DATA_MIXIN_BASE
    val key_of_thm : thm -> term
  ) : ZIPPY_THM_DATA_MIXIN =
struct
open Thm_Data
structure FI = Functor_Instance(FI)
structure MCU = ML_Code_Util
@{parse_entries (struct) PA [add, del]}

val key_of_thm = key_of_thm
val term_value_thm = snd #> #thm
val term_value_data = snd #> #data

fun insert thm data = Data.insert (key_of_thm thm, {thm = Thm.trim_context thm, data = data})
fun delete thm select = Data.delete (key_of_thm thm, select)

val binding = Binding.make (FI.id, FI.pos)

val arg_parsers = {
  add = SOME (Parse_Util.nonempty_code (K "data to add must not be empty")),
  del = SOME (Parse_Util.nonempty_code (K "selector for deletion must not be empty"))
}

val parse_arg_entries =
  let
    val parse_value = PA.parse_entry (PA.get_add arg_parsers) (PA.get_del arg_parsers)
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key Parse_Util.eq parse_value
  in PA.parse_entries_required Parse.and_list1 [] parse_entry (PA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun default (context, _) = (SOME context, NONE)
    fun run_code code = (fn thm => Term_Util.no_dummy_pattern (Thm.prop_of thm) ?
      (Thm.attribute_declaration (ML_Attribute.run_declaration_attribute (code, pos)) thm))
      |> Thm.declaration_attribute
    fun run_dep_app f c =
      let
        val thm = MCU.internal_name "thm" |> MCU.read
        val context = MCU.internal_name "context" |> MCU.read
      in
        MCU.read "fn" @ thm @ MCU.read "=>" @ MCU.read "fn" @ context @ MCU.read "=>" @ f @ thm @
          MCU.atomic (MCU.atomic c @ thm @ context) @ context
        |> run_code
      end
    val add = case PA.get_add_safe entries of
        SOME c => run_dep_app (FI.code_struct_op "insert") c
      | NONE => default
    val del = case PA.get_del_safe entries of
        SOME c => run_dep_app (FI.code_struct_op "delete") c
      | NONE => default
  in ML_Attribute_Util.apply_attribute del #> add end

val parse_attribute = (parse_arg_entries |> Parse_Util.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("add/del theorem data " ^ enclose "(" ")" FI.long_name)
end
