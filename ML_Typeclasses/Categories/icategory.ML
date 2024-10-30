(*  Title:  icategory.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses related to category theory,
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature ISEMI_CATEGORY_BASE =
sig

type ('i, 'o, 'a, 'b) cat
val comp : ('j, 'k, 'b, 'c) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'k, 'a, 'c) cat

end

functor ISemi_Category_Semi_Category(SC : SEMI_CATEGORY_BASE) : ISEMI_CATEGORY_BASE =
struct
open SC
type ('i, 'j, 'a, 'b) cat = ('a, 'b) SC.cat
end

functor Semi_Category_ISemi_Category(
    structure SC : ISEMI_CATEGORY_BASE
    structure T : GROUND_TYPE
  ) : SEMI_CATEGORY_BASE =
struct
open SC
type ('a, 'b) cat = (T.t, T.t, 'a, 'b) SC.cat
end

signature ISEMI_CATEGORY =
sig

include ISEMI_CATEGORY_BASE
val >>> : ('i, 'j, 'a, 'b) cat * ('j, 'k, 'b, 'c) cat -> ('i, 'k, 'a, 'c) cat
val o : ('j, 'k, 'b, 'c) cat * ('i, 'j, 'a, 'b) cat -> ('i, 'k, 'a, 'c) cat

end

functor ISemi_Category(C : ISEMI_CATEGORY_BASE) : ISEMI_CATEGORY =
struct

open C
fun f >>> g = comp g f
fun f o g = comp f g

end

signature ILAZY_COMP =
sig

include ISEMI_CATEGORY_BASE
val comp_lazy : (unit -> ('j, 'k, 'b, 'c) cat) -> ('i, 'j, 'a, 'b) cat -> ('i, 'k, 'a, 'c) cat

end

functor ILazy_Comp_Lazy_Comp(L : LAZY_COMP) : ILAZY_COMP =
struct
open L
structure SC = ISemi_Category_Semi_Category(L)
open SC
end

functor Lazy_Comp_ILazy_Comp(
    structure L : ILAZY_COMP
    structure T : GROUND_TYPE
  ) : LAZY_COMP =
struct
open L
structure SC = Semi_Category_ISemi_Category(structure SC = L; structure T = T)
open SC
end

signature ICATEGORY_BASE =
sig

include ISEMI_CATEGORY_BASE

(*unit argument to fight ML's value restriction*)
val id : unit -> ('i, 'i, 'a, 'a) cat

end

functor ICategory_Category(C : CATEGORY_BASE) : ICATEGORY_BASE =
struct
open C
structure SC = ISemi_Category_Semi_Category(C)
open SC
end

functor Category_ICategory(
    structure C : ICATEGORY_BASE
    structure T : GROUND_TYPE
  ) : CATEGORY_BASE =
struct
open C
structure SC = Semi_Category_ISemi_Category(structure SC = C; structure T = T)
open SC
end

signature ICATEGORY =
sig

include ICATEGORY_BASE
val repeatn : int -> ('i, 'i, 'a, 'a) cat -> ('i, 'i, 'a, 'a) cat

end

functor ICategory(C : ICATEGORY_BASE) : ICATEGORY =
struct

open C

fun repeatn n f = if n <= 0 then id () else comp (repeatn (n - 1) f) f

end

signature IARROW_BASE =
sig

include ICATEGORY_BASE
val arr : ('a -> 'b) -> ('i, 'i, 'a, 'b) cat
val *** : ('i, 'j, 'a, 'b) cat * ('j, 'k, 'c, 'd) cat -> ('i, 'k, ('a * 'c), ('b * 'd)) cat

end

functor IArrow_Arrow(A : ARROW_BASE) : IARROW_BASE =
struct
open A
structure C = ICategory_Category(A)
open C
end

functor Arrow_IArrow(structure A : IARROW_BASE; structure T : GROUND_TYPE) : ARROW_BASE =
struct
open A
structure C = Category_ICategory(structure C = A; structure T = T)
open C
end

signature IARROW =
sig

include IARROW_BASE

val first : ('i, 'o, 'a, 'b) cat -> ('i, 'o, ('a * 'c), ('b * 'c)) cat
val second : ('i, 'o, 'a, 'b) cat -> ('i, 'o, ('c * 'a), ('c * 'b)) cat

val &&& : ('i, 'j, 'a, 'b) cat * ('j, 'k, 'a, 'c) cat -> ('i, 'k, 'a, 'b * 'c) cat

val K : 'a -> ('i, 'i, 'b, 'a) cat
val curry : ('i, 'o, 'a * 'b, 'c) cat -> 'a -> ('i, 'o, 'b, 'c) cat

end

functor IArrow(A : IARROW_BASE) : IARROW =
struct

open A
fun first f = f *** id ()
fun second f = id () *** f

fun f &&& g = comp (f *** g) (arr (fn b => (b, b)))

fun K x = arr (fn _ => x)
fun curry m i = comp m (K i &&& id ())

end

signature IARROW_APPLY_BASE =
sig

include IARROW_BASE
val app : ('i, 'j, ('i, 'j, 'a, 'b) cat * 'a, 'b) cat

end

functor IArrow_Apply_Arrow_Apply(AA : ARROW_APPLY_BASE) : IARROW_APPLY_BASE =
struct
open AA
structure A = IArrow_Arrow(AA)
open A
end

functor Arrow_Apply_IArrow_Apply(structure AA : IARROW_APPLY_BASE; structure T : GROUND_TYPE)
  : ARROW_APPLY_BASE =
struct
open AA
structure A = Arrow_IArrow(structure A = AA; structure T = T)
open A
end

signature IARROW_APPLY =
sig

include IARROW_APPLY_BASE
val uncurry : ('a -> ('i, 'j, 'b, 'c) cat) -> ('i, 'j, 'a * 'b, 'c) cat

end

functor IArrow_Apply(A : IARROW_APPLY_BASE) : IARROW_APPLY =
struct

open A
fun uncurry f = A.comp A.app (A.arr (apfst f))

end

signature IARROW_ZERO_BASE =
sig

include IARROW_BASE
val zero : unit -> ('i, 'i, 'a, 'b) cat

end

functor IArrow_Zero_Arrow_Zero(AZ : ARROW_ZERO_BASE) : IARROW_ZERO_BASE =
struct
open AZ
structure A = IArrow_Arrow(AZ)
open A
end

functor Arrow_Zero_IArrow_Zero(structure AZ : IARROW_ZERO_BASE; structure T : GROUND_TYPE)
  : ARROW_ZERO_BASE =
struct
open AZ
structure A = Arrow_IArrow(structure A = AZ; structure T = T)
open A
end

signature IARROW_PLUS_BASE =
sig

include IARROW_ZERO_BASE
val plus : ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat

end

functor IArrow_Plus_Arrow_Plus(AP : ARROW_PLUS_BASE) : IARROW_PLUS_BASE =
struct
open AP
structure A = IArrow_Zero_Arrow_Zero(AP)
open A
end

functor Arrow_Plus_IArrow_Plus(structure AP : IARROW_PLUS_BASE; structure T : GROUND_TYPE)
  : ARROW_PLUS_BASE =
struct
open AP
structure A = Arrow_Zero_IArrow_Zero(structure AZ = AP; structure T = T)
open A
end

signature IARROW_OR_BASE =
sig

include IARROW_ZERO_BASE
val or : ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat

end

functor IArrow_Or_Arrow_Or(AO : ARROW_OR_BASE) : IARROW_OR_BASE =
struct
open AO
structure A = IArrow_Zero_Arrow_Zero(AO)
open A
end

functor Arrow_Or_IArrow_Or(structure AO : IARROW_OR_BASE; structure T : GROUND_TYPE)
  : ARROW_OR_BASE =
struct
open AO
structure A = Arrow_Zero_IArrow_Zero(structure AZ = AO; structure T = T)
open A
end

signature IARROW_EXCEPTION_BASE =
sig

include IARROW_BASE
type exn

val throw : ('i, 'i, exn, 'a) cat
val catch : ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a * exn, 'b) cat -> ('i, 'j, 'a, 'b) cat

end

functor IArrow_Exception_Arrow_Exception(AE : ARROW_EXCEPTION_BASE)
  : IARROW_EXCEPTION_BASE =
struct
open AE
structure A = IArrow_Arrow(AE)
open A
end

functor Arrow_Exception_IArrow_Exception(structure AE : IARROW_EXCEPTION_BASE; structure T : GROUND_TYPE)
  : ARROW_EXCEPTION_BASE =
struct
open AE
structure A = Arrow_IArrow(structure A = AE; structure T = T)
open A
end

signature IARROW_EXCEPTION =
sig

include IARROW_EXCEPTION_BASE

val throw' : exn -> ('i, 'i, 'a, 'b) cat
val catch' : ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a, 'b) cat
val try : ('i, 'i, 'a, 'a) cat -> ('i, 'i, 'a, 'a) cat

end

functor IArrow_Exception(A : IARROW_EXCEPTION_BASE) : IARROW_EXCEPTION =
struct

open A

fun throw' x = comp throw (arr (K x))
fun catch' f g = catch f (comp g (arr fst))
fun try f = catch' f (id ())

end

signature IARROW_CHOICE_BASE =
sig

include IARROW_BASE
val cases : ('i, 'j, 'a, 'c) cat -> ('i, 'j, 'b, 'd) cat ->
  ('i, 'j, ('a, 'b) Either.either, ('c, 'd) Either.either) cat
val merge : ('i, 'j, 'a, 'c) cat -> ('i, 'j, 'b, 'c) cat -> ('i, 'j, ('a, 'b) Either.either, 'c) cat

end

functor IArrow_Choice_Arrow_Choice(AC : ARROW_CHOICE_BASE) : IARROW_CHOICE_BASE =
struct
open AC
structure A = IArrow_Arrow(AC)
open A
end

functor Arrow_Choice_IArrow_Choice(structure AC : IARROW_CHOICE_BASE; structure T : GROUND_TYPE)
  : ARROW_CHOICE_BASE =
struct
open AC
structure A = Arrow_IArrow(structure A = AC; structure T = T)
open A
end

signature IARROW_CHOICE =
sig

include IARROW_CHOICE_BASE
val opt : ('i, 'j, unit, 'b) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'j, 'a option, 'b) cat

end

functor IArrow_Choice(A : IARROW_CHOICE_BASE) : IARROW_CHOICE =
struct

open A
fun opt fnone fsome = comp (merge fnone fsome) (arr Either.of_opt)

end
