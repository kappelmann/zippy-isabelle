(*  Title:  category.ML
    Author: Kevin Kappelmann

Basic typeclasses related to category theory, inspired by the Haskell base package.
*)
signature CATEGORY_BASE =
sig

type ('a, 'b) cat
(*unit argument to fight ML's value restriction*)
val id : unit -> ('a, 'a) cat
val comp : ('b, 'c) cat -> ('a, 'b) cat -> ('a, 'c) cat

end

signature CATEGORY =
sig

include CATEGORY_BASE
val >>> : ('a, 'b) cat -> ('b, 'c) cat -> ('a, 'c) cat

end

functor Category(C : CATEGORY_BASE) : CATEGORY =
struct

open C
fun >>> f g = comp g f

end

signature ARROW_BASE =
sig

include CATEGORY_BASE
val arr : ('a -> 'b) -> ('a, 'b) cat
val *** : ('a, 'b) cat -> ('c, 'd) cat -> (('a * 'c), ('b * 'd)) cat

end

signature ARROW =
sig

include ARROW_BASE

val first : ('a, 'b) cat -> (('a * 'c), ('b * 'c)) cat
val second : ('a, 'b) cat -> (('c * 'a), ('c * 'b)) cat

val &&& : ('a, 'b) cat -> ('a, 'c) cat -> ('a, ('b * 'c)) cat

val K : 'a -> ('b, 'a) cat
val curry : (('a * 'b), 'c) cat -> 'a -> ('b, 'c) cat

end

functor Arrow(A : ARROW_BASE) : ARROW =
struct

open A
fun first f = *** f (id ())
fun second f = *** (id ()) f

fun &&& f g = comp (A.*** f g) (arr (fn b => (b,b)))

fun K x = arr (fn _ => x)
fun curry m i = comp m (&&& (K i) (id ()))

end

signature ARROW_APPLY_BASE =
sig

include ARROW_BASE
val app : (('a, 'b) cat * 'a, 'b) cat

end

signature ARROW_APPLY =
sig

include ARROW_APPLY_BASE
val uncurry : ('a -> ('b, 'c) cat) -> (('a * 'b), 'c) cat

end

functor Arrow_Apply(A : ARROW_APPLY_BASE) : ARROW_APPLY =
struct

open A
fun uncurry f = A.comp A.app (A.arr (apfst f))

end

signature ARROW_ZERO_BASE =
sig

include ARROW_BASE
val zero : unit -> ('a, 'b) cat

end

signature ARROW_PLUS_BASE =
sig

include ARROW_ZERO_BASE
val plus : ('a, 'b) cat -> ('a, 'b) cat -> ('a, 'b) cat

end
