(*  Title:      Constraint_Logic_Programming/util.ML
    Author:     Kevin Kappelmann

Utilities used for constraint logic programming.
*)

signature CONSTRAINT_LOGIC_PROGRAMMING_UTIL =
sig

  (* miscellaneous *)
  val spaces : string list -> string

  (* parsing *)
  val parse_position : 'a parser -> ('a * Position.T) parser

  (* manipulating parsed ML code *)
  (*type of parsed ML code*)
  type code = ML_Lex.token Antiquote.antiquote list

  val code_flat : code list -> code
  val code_enclose : code -> code -> code -> code
  val code_list_arg : code list -> code

  (*runs passed code, taking context as argument, and returning updated context*)
  val run_context_code : code -> Position.T -> Context.generic -> Context.generic

  (*returns a name variant that ought to avoid name shadowing in antiquotations*)
  val internal_code_name : string -> string

  (*creates code that 1) retrieves context, 2) passes it as first argument
    to the given code, and 3) returns updated context*)
  val update_context_code : code -> code
  (*composition of update_context_code and run_context code*)
  val run_update_context_code : code -> Position.T -> Context.generic -> Context.generic

  (*creates code that 1) retrieves context, 2) passes it to first code argument
    to retrieve data, 3) passes data and context to second code argument, and
    4) returns updated context*)
  val get_data_update_context_code : code -> code -> code
  (*composition of get_data_update_context_code and run_context code*)
  val run_get_data_update_context_code :
    code -> code -> Position.T -> Context.generic -> Context.generic

  (*universal theorem data variable*)
  val univ_thmvar : thm option Universal_Data.var
  (*puts theorem into context*)
  val put_univ_thm : thm -> Context.generic -> Context.generic
  (*retrieves theorem from context*)
  val get_univ_thm_code : code

end

structure Constraint_Logic_Programming_Util
  : CONSTRAINT_LOGIC_PROGRAMMING_UTIL =
struct

(* miscellaneous *)
val spaces = space_implode " "

(* parsing *)
fun parse_position scan =
  (Scan.optional (Scan.ahead Parse.not_eof >> Token.pos_of) Position.none
  >> (snd o Position.default))
  -- scan
  >> swap

(* manipulating parsed ML code *)
type code = ML_Lex.token Antiquote.antiquote list

val code_flat = flat

fun code_enclose start close code = code_flat [start, code, close]

val code_list_arg =
  separate (ML_Lex.read ", ")
  #> code_flat
  #> code_enclose (ML_Lex.read "[") (ML_Lex.read "]")

fun run_context_code code pos = ML_Context.expression pos code

fun internal_code_name name = "INTERNAL___" ^ name

val internal_context_name = internal_code_name "code_context"

fun update_context_code update_code = code_flat [
    ML_Lex.read
      (spaces ["let val", internal_context_name, "= Context.the_generic_context () \n"]),
    ML_Lex.read (spaces ["val", internal_context_name, "= ("]),
    update_code,
    ML_Lex.read (spaces [")",internal_context_name, "\n"]),
    ML_Lex.read
      ("in Context.put_generic_context (SOME " ^ internal_context_name ^ ") end")
  ]
val run_update_context_code = update_context_code #> run_context_code

val internal_data_name = internal_code_name "code_data"

fun get_data_update_context_code get_data_code update_code =
  let val update_code = code_flat [
      ML_Lex.read (spaces ["fn", internal_context_name, "=> \n"]),
      ML_Lex.read (spaces ["let val", internal_data_name, "= ("]),
      get_data_code,
      ML_Lex.read (spaces [")", internal_context_name, "\n"]),
      ML_Lex.read "in (",
      update_code,
      ML_Lex.read (spaces [")", internal_data_name, internal_context_name, "end"])
    ]
  in update_context_code update_code end
fun run_get_data_update_context_code get_data_code =
  get_data_update_context_code get_data_code #> run_context_code

val univ_thmvar : thm option Universal_Data.var =
  Context.>>> (Universal_Data.insert NONE)

val put_univ_thm = Universal_Data.put univ_thmvar o SOME
val get_univ_thm_code =
  ML_Lex.read "the o Universal_Data.get Constraint_Logic_Programming_Util.univ_thmvar"

end

