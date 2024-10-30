(*  Title:  icategory_util.ML
    Author: Kevin Kappelmann

Utilities on indexed categories
*)
signature IARROW_EXCEPTION_REC =
sig

include IARROW_EXCEPTION
val repeat : ('i, 'i, 'a, 'a) cat -> ('i, 'i, 'a, 'a) cat
val try_step : ('i, 'j, 'a, 'b) cat -> ('i, 'i, 'a, 'a) cat -> ('i, 'j, 'a, 'b) cat

end

functor IArrow_Exception_Rec(
    structure A : IARROW_EXCEPTION
    structure L : ILAZY_COMP
    sharing type L.cat = A.cat
  ) : IARROW_EXCEPTION_REC =
struct

open A

fun repeat move = try (L.comp_lazy (fn _ => repeat move) move)
fun try_step f step = catch' f (L.comp_lazy (fn _ => try_step f step) step)

end

signature IARROW_FOLD =
sig
  include IARROW_BASE

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a

  val fold : ('j, 'i, 'a, 'a) cat -> ('i, 'j, 'a * 'b, 'b res) cat ->
    ('i, 'j, 'a * 'b, 'b res) cat

  val fold_init : ('i, 'i, 'a, 'a) cat -> ('i, 'i, 'a * 'b, 'b res) cat ->
    ('i, 'i, 'a, 'b res) cat -> ('i, 'i, 'a, 'b res) cat
end

functor IArrow_Fold_Exception_Choice(
    structure A : IARROW
    structure AE : IARROW_EXCEPTION_REC
    sharing type AE.cat = A.cat
    structure AC : IARROW_CHOICE_BASE
    sharing type AC.cat = A.cat
    structure L : ILAZY_COMP
    sharing type L.cat = A.cat
  ) : IARROW_FOLD =
struct

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

open A

local structure SC = ISemi_Category(AE) open SC
in

fun fold_step next cont = arr (fn (_, res as Stop _) => Either.Left res | x => Either.Right x)
  >>> AC.merge (id ()) (AE.catch' (L.comp_lazy cont (next *** arr dest_res)) (arr snd))

fun fold next update = arr fst &&& update >>> fold_step next (fn _ => fold next update)

fun fold_init next update init = AE.try_step (id () &&& init) next
  >>> fold_step next (fn _ => fold next update)

end

end
