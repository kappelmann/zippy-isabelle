(*  Title:      Zippy/zippy_identifier.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_IDENTIFIER =
sig
  type id = binding
  val eq_id : id * id -> bool
  val pretty_id : id -> Pretty.T
  val quoted_string : id -> string
  val combine_with : string -> id list -> id
  val combine : id list -> id
end

structure Zippy_Identifier : ZIPPY_IDENTIFIER  =
struct

type id = binding
val eq_id = Binding.eq_name
val pretty_id = Binding.pretty
val quoted_string = Binding.print

(*generalised from Binding.ML*)
fun combine_with _ [b] = b
  | combine_with sep bs = Binding.name
    (space_implode sep (map Binding.name_of (filter_out Binding.is_empty bs)))
val combine = combine_with " "

end
