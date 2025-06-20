(*  Title:      Zippy/zippy_action_result.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_RESULT =
sig
  datatype ('s, 'e, 't) result = Stagnate of 's | Expand of 'e | Trim of 't
  val stagnate : 's -> ('s, 'e, 't) result
  val expand : 'e -> ('s, 'e, 't) result
  val trim : 't -> ('s, 'e, 't) result
  val merge : ('s -> 'a) -> ('e -> 'a) -> ('t -> 'a) -> ('s, 'e, 't) result -> 'a
end

structure Zippy_Action_Result : ZIPPY_ACTION_RESULT =
struct
datatype ('s, 'e, 't) result = Stagnate of 's | Expand of 'e | Trim of 't
val stagnate = Stagnate
val expand = Expand
val trim = Trim
fun merge f _ _ (Stagnate s) = f s
  | merge _ f _ (Expand e) = f e
  | merge _ _ f (Trim t) = f t
end
