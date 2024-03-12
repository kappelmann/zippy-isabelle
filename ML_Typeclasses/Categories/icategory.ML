(*  Title:  icategory.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses related to category theory,
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature ICATEGORY_BASE =
sig

type ('i, 'o, 'a, 'b) cat
(*unit argument to fight ML's value restriction*)
val id : unit -> ('i, 'i, 'a, 'a) cat
val comp : ('j, 'k, 'b, 'c) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'k, 'a, 'c) cat

end

functor Category_ICategory(
    structure IC : ICATEGORY_BASE;
    structure T : GROUND_TYPE
  ) : CATEGORY_BASE =
struct

type ('a, 'b) cat = (T.t, T.t, 'a, 'b) IC.cat
val id = IC.id
val comp = IC.comp

end

signature ICATEGORY =
sig

include ICATEGORY_BASE
val >>> : ('i, 'j, 'a, 'b) cat -> ('j, 'k, 'b, 'c) cat -> ('i, 'k, 'a, 'c) cat

end

functor ICategory(IC : ICATEGORY_BASE) : ICATEGORY =
struct

open IC
fun >>> f g = comp g f

end

signature IARROW_BASE =
sig

include ICATEGORY_BASE
val arr : ('a -> 'b) -> ('i, 'i, 'a, 'b) cat
val *** : ('i, 'j, 'a, 'b) cat -> ('j, 'k, 'c, 'd) cat -> ('i, 'k, ('a * 'c), ('b * 'd)) cat

end

functor Arrow_IArrow(structure IA : IARROW_BASE; structure T : GROUND_TYPE) : ARROW_BASE =
struct

structure C = Category_ICategory(structure IC = IA; structure T = T)
open C
val arr = IA.arr
val *** = IA.***

end

signature IARROW =
sig

include IARROW_BASE

val first : ('i, 'o, 'a, 'b) cat -> ('i, 'o, ('a * 'c), ('b * 'c)) cat
val second : ('i, 'o, 'a, 'b) cat -> ('i, 'o, ('c * 'a), ('c * 'b)) cat

val &&& : ('i, 'j, 'a, 'b) cat -> ('j, 'k, 'a, 'c) cat -> ('i, 'k, 'a, 'b * 'c) cat

val K : 'a -> ('i, 'i, 'b, 'a) cat
val curry : ('i, 'o, 'a * 'b, 'c) cat -> 'a -> ('i, 'o, 'b, 'c) cat

end

functor IArrow(IA : IARROW_BASE) : IARROW =
struct

open IA
fun first f = *** f (id ())
fun second f = *** (id ()) f

fun &&& f g = comp (IA.*** f g) (arr (fn b => (b,b)))

fun K x = arr (fn _ => x)
fun curry m i = comp m (&&& (K i) (id ()))

end

signature IARROW_APPLY_BASE =
sig

include IARROW_BASE
val app : ('i, 'j, ('i, 'j, 'a, 'b) cat * 'a, 'b) cat

end

functor Arrow_Apply_IArrow_Apply(structure IAA : IARROW_APPLY_BASE; structure T : GROUND_TYPE)
  : ARROW_APPLY_BASE =
struct

structure A = Arrow_IArrow(structure IA = IAA; structure T = T)
open A
val app = IAA.app

end

signature IARROW_APPLY =
sig

include IARROW_APPLY_BASE
val uncurry : ('a -> ('i, 'j, 'b, 'c) cat) -> ('i, 'j, 'a * 'b, 'c) cat

end

functor IArrow_Apply(IA : IARROW_APPLY_BASE) : IARROW_APPLY =
struct

open IA
fun uncurry f = IA.comp IA.app (IA.arr (apfst f))

end

signature IARROW_ZERO_BASE =
sig

include IARROW_BASE
val zero : unit -> ('i, 'i, 'a, 'b) cat

end

functor Arrow_Zero_IArrow_Zero(structure IAZ : IARROW_ZERO_BASE; structure T : GROUND_TYPE)
  : ARROW_ZERO_BASE =
struct

structure A = Arrow_IArrow(structure IA = IAZ; structure T = T)
open A
val zero = IAZ.zero

end

signature IARROW_PLUS_BASE =
sig

include IARROW_ZERO_BASE
val plus : ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat

end

functor Arrow_Plus_IArrow_Plus(structure IAP : IARROW_PLUS_BASE; structure T : GROUND_TYPE)
  : ARROW_PLUS_BASE =
struct

structure A = Arrow_Zero_IArrow_Zero(structure IAZ = IAP; structure T = T)
open A
val plus = IAP.plus

end
