(*  Title:      HOCLP/zippy_identifier.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_IDENTIFIER =
sig
  type id = binding
  val eq_id : id * id -> bool
  val pretty_id : id -> Pretty.T
end

structure Zippy_Identifier : ZIPPY_IDENTIFIER  =
struct

type id = binding
val eq_id = Binding.eq_name
val pretty_id = Binding.pretty

end
