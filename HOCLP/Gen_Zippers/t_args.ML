(*  Title:      HOCLP/t_args.ML
    Author:     Kevin Kappelmann
*)
signature T_ARGS =
sig
  structure Para : ARGS_ANTIQUOTATIONS
  structure Poly : ARGS_ANTIQUOTATIONS
  structure All : ARGS_ANTIQUOTATIONS

  val Para_nargs : unit -> int
  val Poly_nargs : unit -> int
  val All_nargs : unit -> int
  val Para_nargs' : unit -> string
  val Poly_nargs' : unit -> string
  val All_nargs' : unit -> string
  val suffix_Para_nargs : string -> string
  val suffix_Poly_nargs : string -> string
  val suffix_All_nargs : string -> string

  val succ_mod_Poly_nargs : int -> int
  val pred_mod_Poly_nargs : int -> int
  val succ_mod_Poly_nargs' : int -> string
  val pred_mod_Poly_nargs' : int -> string
end

structure T_Args : T_ARGS =
struct

structure Para = Para_Type_Args_Antiquotations
structure Poly = Poly_Type_Args_Antiquotations
structure All = Type_Args_Antiquotations

val Para_nargs = Context.the_generic_context #> Para.nargs
val Poly_nargs = Context.the_generic_context #> Poly.nargs
val All_nargs = Context.the_generic_context #> All.nargs

val Para_nargs' = Para_nargs #> string_of_int
val Poly_nargs' = Poly_nargs #> string_of_int
val All_nargs' = All_nargs #> string_of_int

fun suffix_Para_nargs n = suffix (Para_nargs' ()) n
fun suffix_Poly_nargs n = suffix (Poly_nargs' ()) n
fun suffix_All_nargs n = suffix (All_nargs' ()) n

fun succ_mod_Poly_nargs i = (i mod Poly_nargs ()) + 1
fun pred_mod_Poly_nargs i = ((i - 2) mod Poly_nargs ()) + 1
val succ_mod_Poly_nargs' = succ_mod_Poly_nargs #> string_of_int
val pred_mod_Poly_nargs' = pred_mod_Poly_nargs #> string_of_int

end
