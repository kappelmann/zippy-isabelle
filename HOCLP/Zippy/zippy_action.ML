(*  Title:      HOCLP/zippy_action.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION =
sig
  type ('a, 'd) action
end

structure Zippy_Action : ZIPPY_ACTION =
struct

datatype ('a, 'd) action = Action of {
    action : 'a,
    data : 'd
  }

fun mk_action action data = Action {action = action, data = data}

end
