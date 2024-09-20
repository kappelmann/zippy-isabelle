(*  Title:  category.ML
    Author: Kevin Kappelmann

Basic typeclasses related to category theory, inspired by the Haskell base package.
*)
infix 1 >>>
infix 1 ***
infix 1 &&&

signature SEMI_CATEGORY_BASE =
sig

type ('a, 'b) cat
val comp : ('b, 'c) cat -> ('a, 'b) cat -> ('a, 'c) cat
val comp_lazy : (unit -> ('b, 'c) cat) -> ('a, 'b) cat -> ('a, 'c) cat

end

signature SEMI_CATEGORY =
sig

include SEMI_CATEGORY_BASE
val >>> : ('a, 'b) cat * ('b, 'c) cat -> ('a, 'c) cat
val o : ('b, 'c) cat * ('a, 'b) cat -> ('a, 'c) cat

end

functor Semi_Category(SC : SEMI_CATEGORY_BASE) : SEMI_CATEGORY =
struct

open SC
fun f >>> g = comp g f
fun f o g = comp f g

end

signature CATEGORY_BASE =
sig

include SEMI_CATEGORY_BASE

(*unit argument to fight ML's value restriction*)
val id : unit -> ('a, 'a) cat

end

signature ARROW_BASE =
sig

include CATEGORY_BASE
val arr : ('a -> 'b) -> ('a, 'b) cat
val *** : ('a, 'b) cat * ('c, 'd) cat -> (('a * 'c), ('b * 'd)) cat

end

signature ARROW =
sig

include ARROW_BASE

val first : ('a, 'b) cat -> (('a * 'c), ('b * 'c)) cat
val second : ('a, 'b) cat -> (('c * 'a), ('c * 'b)) cat

val &&& : ('a, 'b) cat * ('a, 'c) cat -> ('a, ('b * 'c)) cat

val K : 'a -> ('b, 'a) cat
val curry : (('a * 'b), 'c) cat -> 'a -> ('b, 'c) cat

end

functor Arrow(A : ARROW_BASE) : ARROW =
struct

open A
fun first f = f *** id ()
fun second f = id () *** f

fun f &&& g = comp (f *** g) (arr (fn b => (b, b)))

fun K x = arr (fn _ => x)
fun curry f i = comp f (K i &&& id ())

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

signature ARROW_OR_BASE =
sig

include ARROW_ZERO_BASE
val or : ('a, 'b) cat -> ('a, 'b) cat -> ('a, 'b) cat

end

signature ARROW_EXCEPTION_BASE =
sig

include ARROW_BASE
type exn

val throw : (exn, 'a) cat
val catch : ('a, 'b) cat -> ('a * exn, 'b) cat -> ('a, 'b) cat

end

signature ARROW_EXCEPTION =
sig

include ARROW_EXCEPTION_BASE

val catch' : ('a, 'b) cat -> ('a, 'b) cat -> ('a, 'b) cat
val try : ('a, 'a) cat -> ('a, 'a) cat
val repeat : ('a, 'a) cat -> ('a, 'a) cat

end

functor Arrow_Exception(A : ARROW_EXCEPTION_BASE) : ARROW_EXCEPTION =
struct

open A

fun catch' f g = catch f (comp g (arr fst))
fun try f = catch' f (id ())
fun repeat move = try (comp_lazy (fn _ => repeat move) move)

end

signature ARROW_CHOICE_BASE =
sig

include ARROW_BASE
val cases : ('a, 'c) cat -> ('b, 'd) cat -> (('a, 'b) Either.either, ('c, 'd) Either.either) cat
val merge : ('a, 'c) cat -> ('b, 'c) cat -> (('a, 'b) Either.either, 'c) cat

end

signature ARROW_CHOICE =
sig

include ARROW_CHOICE_BASE
val opt : (unit, 'b) cat -> ('a, 'b) cat -> ('a option, 'b) cat

end

functor Arrow_Choice(A : ARROW_CHOICE_BASE) : ARROW_CHOICE =
struct

open A
fun opt fnone fsome = comp (merge fnone fsome) (arr Either.of_opt)

end

