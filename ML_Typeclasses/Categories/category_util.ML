(*  Title:  category_util.ML
    Author: Kevin Kappelmann

Utilities on categories
*)
signature ARROW_EXCEPTION_REC =
sig
  include ARROW_EXCEPTION
  val repeat : ('p1, 'a, 'a) cat -> ('p1, 'a, 'a) cat
  val try_step : ('p1, 'a, 'b) cat -> ('p1, 'a, 'a) cat -> ('p1, 'a, 'b) cat
end

functor Arrow_Exception_Rec(
    structure A : ARROW_EXCEPTION
    structure L : LAZY_COMP
    sharing type L.cat = A.cat
  ) : ARROW_EXCEPTION_REC =
struct

open A

fun repeat move = try (L.comp_lazy (fn _ => repeat move) move)
fun try_step f step = catch' f (L.comp_lazy (fn _ => try_step f step) step)

end

signature ARROW_FOLD =
sig
  include ARROW_BASE

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a

  val fold : ('p1, 'a, 'a) cat -> ('p1, 'a * 'b, 'b res) cat ->
    ('p1, 'a * 'b, 'b res) cat

  val fold_init : ('p1, 'a, 'a) cat -> ('p1, 'a * 'b, 'b res) cat ->
    ('p1, 'a, 'b res) cat -> ('p1, 'a, 'b res) cat
end

functor Arrow_Fold_Exception_Choice(
    structure A : ARROW
    structure AE : ARROW_EXCEPTION_REC
    sharing type AE.cat = A.cat
    structure AC : ARROW_CHOICE_BASE
    sharing type AC.cat = A.cat
    structure L : LAZY_COMP
    sharing type L.cat = A.cat
  ) : ARROW_FOLD =
struct

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

open A

local structure SC = Semi_Category(AE) open SC
in

fun fold_step next cont = arr (fn (_, res as Stop _) => Either.Left res | x => Either.Right x)
  >>> AC.merge (id ()) (AE.catch' (L.comp_lazy cont (next *** arr dest_res)) (arr snd))

fun fold next update = arr fst &&& update >>> fold_step next (fn _ => fold next update)

fun fold_init next update init = AE.try_step (id () &&& init) next
  >>> fold_step next (fn _ => fold next update)

end

end
