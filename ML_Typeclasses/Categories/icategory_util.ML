(*  Title:  icategory_util.ML
    Author: Kevin Kappelmann

Utilities on indexed categories
*)
signature IARROW_FOLD =
sig
  structure AE : IARROW_EXCEPTION_BASE
  structure AC : IARROW_CHOICE_BASE
  sharing type AC.cat = AE.cat

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a

  val fold : ('j, 'i, 'a, 'a) AE.cat -> ('i, 'j, 'a * 'b, 'b res) AE.cat ->
    ('i, 'j, 'a * 'b, 'b) AE.cat
end

functor IArrow_Fold(
    structure AE : IARROW_EXCEPTION
    structure AC : IARROW_CHOICE_BASE
    sharing type AC.cat = AE.cat
  ) : IARROW_FOLD =
struct

structure AE = AE
structure AC = AC

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

local structure SC = ISemi_Category(AE) structure A = IArrow(AE) open A SC
in
fun fold next update =
  arr fst &&& update
  >>> arr (fn (_, Stop acc) => Either.Left acc | (x, Continue acc) => Either.Right (x, acc))
  >>> AC.merge (id ()) (AE.catch' (comp_lazy (fn _ => fold next update) (first next)) (arr snd))
end

end
