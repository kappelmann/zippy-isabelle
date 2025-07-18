(*  Title:      Zippy/zippy_action_result.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_RESULT =
sig
  datatype ('s, 'e, 't) result = Unchanged of 's (*stay at node without structural changes*)
    | Expanded of 'e (*expand without changing existing node paths*)
    | Changed of 't (*other structural changes*)
  val merge : ('s -> 'a) -> ('e -> 'a) -> ('t -> 'a) -> ('s, 'e, 't) result -> 'a
end

structure Zippy_Action_Result : ZIPPY_ACTION_RESULT =
struct
datatype ('s, 'e, 't) result = Unchanged of 's | Expanded of 'e | Changed of 't
fun merge f _ _ (Unchanged s) = f s
  | merge _ f _ (Expanded e) = f e
  | merge _ _ f (Changed t) = f t
end
