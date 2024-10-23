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
    ('i, 'j, 'a * 'b, 'b res) AE.cat

  val fold_init : ('i, 'i, 'a, 'a) AE.cat -> ('i, 'i, 'a * 'b, 'b res) AE.cat ->
    ('i, 'i, 'a, 'b res) AE.cat -> ('i, 'i, 'a, 'b res) AE.cat

end

functor IArrow_Fold(
    structure A : IARROW
    structure AE : IARROW_EXCEPTION
    sharing type AE.cat = A.cat
    structure AC : IARROW_CHOICE_BASE
    sharing type AC.cat = A.cat
  ) : IARROW_FOLD =
struct

structure AE = AE
structure AC = AC

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

local structure SC = ISemi_Category(AE) open A SC
in

fun fold_step next cont = arr (fn (_, res as Stop _) => Either.Left res | x => Either.Right x)
  >>> AC.merge (id ()) (AE.catch' (comp_lazy cont (next *** arr dest_res)) (arr snd))

fun fold next update = arr fst &&& update >>> fold_step next (fn _ => fold next update)

fun fold_init next update init = AE.try_step (id () &&& init) next
  >>> fold_step next (fn _ => fold next update)

end

end
